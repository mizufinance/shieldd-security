"""Additional crash-recovery guards; never change a frozen runner or plan.

The outer Windows job owns the controller and its Lean descendant, including
preflight hashing. Closing this supervisor kills only that owned process tree.
Admission denial launches nothing and does not alter any proof receipt.
"""
import argparse
import ctypes as C
from ctypes import wintypes as W
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import threading

sys.dont_write_bytecode = True
D = Path(__file__).resolve().parent
RUNNER_SHA = '32e3856ab841004a8485435e423cac3ae407d84da227b44750ca7ce803ceda9c'
EXPANDED_RUNNER_SHA = RUNNER_SHA
MIB = 1024 ** 2
RUNNING_RAM, RUNNING_COMMIT, GROUP_CAP = 1536 * MIB, 1024 * MIB, 10240 * MIB
# User removed the former 8GiB admission floor. No additional startup reserve:
# admission uses the same pressure-stop levels monitored throughout the run.
ADMISSION_RAM, ADMISSION_COMMIT = RUNNING_RAM, RUNNING_COMMIT


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def telemetry(api, kernel, psapi):
    mem = api.MEMORYSTATUSEX(); mem.length = C.sizeof(mem)
    perf = api.PERFORMANCE_INFORMATION(); perf.cb = C.sizeof(perf)
    if not kernel.GlobalMemoryStatusEx(C.byref(mem)) or not psapi.GetPerformanceInfo(C.byref(perf), perf.cb):
        raise RuntimeError('Memory telemetry unavailable')
    return mem.availPhys, (perf.CommitLimit - perf.CommitTotal) * perf.PageSize


def inventory(kernel):
    class ENTRY(C.Structure):
        _fields_ = [('size', W.DWORD), ('usage', W.DWORD), ('pid', W.DWORD),
                    ('heap', C.c_size_t), ('module', W.DWORD), ('threads', W.DWORD),
                    ('parent', W.DWORD), ('priority', W.LONG), ('flags', W.DWORD),
                    ('exe', W.WCHAR * 260)]
    kernel.CreateToolhelp32Snapshot.argtypes = [W.DWORD, W.DWORD]
    kernel.CreateToolhelp32Snapshot.restype = W.HANDLE
    kernel.Process32FirstW.argtypes = [W.HANDLE, C.POINTER(ENTRY)]
    kernel.Process32NextW.argtypes = [W.HANDLE, C.POINTER(ENTRY)]
    snapshot = kernel.CreateToolhelp32Snapshot(2, 0)
    if snapshot == C.c_void_p(-1).value: raise C.WinError(C.get_last_error())
    rows = []
    try:
        entry = ENTRY(); entry.size = C.sizeof(entry)
        ok = kernel.Process32FirstW(snapshot, C.byref(entry))
        if not ok: raise RuntimeError('Process inventory unavailable')
        while ok:
            rows.append((entry.pid, entry.exe.lower(), entry.parent))
            ok = kernel.Process32NextW(snapshot, C.byref(entry))
    finally:
        kernel.CloseHandle(snapshot)
    return rows


def owned_job(api, kernel, memory_cap):
    job = kernel.CreateJobObjectW(None, None)
    if not job: raise C.WinError(C.get_last_error())
    limits = api.EXTENDED_LIMIT()
    limits.Basic.LimitFlags = 0x2000 | 0x200 | 0x8
    limits.Basic.ActiveProcessLimit = 2
    limits.JobMemoryLimit = memory_cap
    if not kernel.SetInformationJobObject(job, 9, C.byref(limits), C.sizeof(limits)):
        kernel.CloseHandle(job)
        raise C.WinError(C.get_last_error())
    return job


def owned_private_commit(api, kernel, psapi, controller_pid, job):
    rows = inventory(kernel)
    owned = {pid for pid, _, parent in rows if pid == controller_pid or parent == controller_pid}
    kernel.OpenProcess.argtypes = [W.DWORD, W.BOOL, W.DWORD]
    kernel.OpenProcess.restype = W.HANDLE
    kernel.IsProcessInJob.argtypes = [W.HANDLE, W.HANDLE, C.POINTER(W.BOOL)]
    total = count = primary_count = 0
    members = []
    for pid in owned:
        handle = kernel.OpenProcess(0x1000, False, pid)
        if not handle:
            if C.get_last_error() == 87: continue  # Process exited after inventory.
            raise C.WinError(C.get_last_error())
        try:
            belongs = W.BOOL()
            if not kernel.IsProcessInJob(handle, job, C.byref(belongs)):
                raise RuntimeError('Owned-job membership telemetry unavailable')
            if not belongs.value: continue
            count += 1
            members.append(next(row for row in rows if row[0] == pid))
            # Windows also assigns its headless console host to the job.
            # Account for that helper without permitting another verifier.
            if members[-1][1] != 'conhost.exe': primary_count += 1
            if primary_count > 2 or count > 4:
                raise RuntimeError('Unexpected owned process count: ' + repr(members))
        finally:
            kernel.CloseHandle(handle)
        handle = kernel.OpenProcess(0x410, False, pid)
        if not handle:
            if C.get_last_error() == 87: continue
            raise C.WinError(C.get_last_error())
        try:
            counters = api.PROCESS_MEMORY_COUNTERS(); counters.cb = C.sizeof(counters)
            if not psapi.GetProcessMemoryInfo(handle, C.byref(counters), counters.cb):
                raise RuntimeError('Owned private-commit telemetry unavailable')
            total += counters.PagefileUsage
        finally:
            kernel.CloseHandle(handle)
    return total


def effective_commit_cap(current, ram, commit):
    extra = min(ram - RUNNING_RAM, commit - RUNNING_COMMIT)
    if extra < 0: raise RuntimeError('Host reserve pressure')
    return min(GROUP_CAP, max(64 * MIB, current + extra))


def update_owned_job_limit(api, kernel, job, memory_cap):
    limits = api.EXTENDED_LIMIT()
    limits.Basic.LimitFlags = 0x2000 | 0x200 | 0x8
    limits.Basic.ActiveProcessLimit = 2
    limits.JobMemoryLimit = memory_cap
    if not kernel.SetInformationJobObject(job, 9, C.byref(limits), C.sizeof(limits)):
        raise C.WinError(C.get_last_error())


def main():
    global RUNNING_RAM, RUNNING_COMMIT, GROUP_CAP, ADMISSION_RAM, ADMISSION_COMMIT
    parser = argparse.ArgumentParser()
    parser.add_argument('folder')
    parser.add_argument('--check-only', action='store_true')
    parser.add_argument('--execute-reviewed-plan-sha256')
    args = parser.parse_args()
    root = (D / args.folder).resolve()
    if root.parent != D: raise SystemExit('Only a direct diagnostics task folder is allowed')
    runner = root / 'execute_bounded.py'
    runner_sha = digest(runner)
    if runner_sha not in {RUNNER_SHA, EXPANDED_RUNNER_SHA}:
        raise SystemExit('Frozen runner identity changed')
    if runner_sha == EXPANDED_RUNNER_SHA:
        RUNNING_RAM, RUNNING_COMMIT, GROUP_CAP = 1536 * MIB, 1024 * MIB, 10240 * MIB
        ADMISSION_RAM, ADMISSION_COMMIT = RUNNING_RAM, RUNNING_COMMIT
    # Reject an interrupted or previously run folder before any broad hashing.
    if (root / 'events.jsonl').exists() and (root / 'events.jsonl').stat().st_size:
        raise SystemExit('Existing attempt retained; fresh plan required')
    review = json.loads((root / 'review.json').read_bytes())
    plan_sha = digest(root / 'plan.json')
    if plan_sha != review['plan']['sha256']: raise SystemExit('Reviewed plan identity changed')
    if runner_sha == EXPANDED_RUNNER_SHA:
        plan = json.loads((root / 'plan.json').read_bytes())
        if plan['limits']['heap_mib'] != 8192 or plan['pressure_limits']['owned_job_memory_and_rss_bytes'] != 12 * 1024**3:
            raise SystemExit('Expanded-memory profile mismatch')
    spec = importlib.util.spec_from_file_location('frozen_runner', runner)
    api = importlib.util.module_from_spec(spec); spec.loader.exec_module(api)
    kernel, psapi = api.winapi()
    ram, commit = telemetry(api, kernel, psapi)
    forbidden = {'lean.exe', 'lake.exe', 'cargo.exe', 'rustc.exe', 'quint.exe', 'tlc.exe'}
    if any(name in forbidden for _, name, _ in inventory(kernel)):
        raise SystemExit('Existing heavy verification; no job launched')
    eligible = ram >= ADMISSION_RAM and commit >= ADMISSION_COMMIT
    print(json.dumps({'event': 'admission_snapshot', 'free_ram_mib': ram // MIB,
                      'commit_headroom_mib': commit // MIB, 'eligible_now': eligible,
                      'stable_seconds_required': 60, 'plan_sha256': plan_sha,
                      'memory_profile': 'expanded8192',
                      'whole_group_commit_cap_mib': GROUP_CAP // MIB,
                      'running_ram_floor_mib': RUNNING_RAM // MIB,
                      'running_commit_floor_mib': RUNNING_COMMIT // MIB}), flush=True)
    if args.check_only: return
    if args.execute_reviewed_plan_sha256 != plan_sha:
        raise SystemExit('Explicit reviewed plan hash required')
    if not eligible: raise SystemExit('Resource hold; no job launched')
    mutex = kernel.CreateMutexW(None, False, 'Global\\ShielddFormalCrashRecoverySupervisor')
    if not mutex: raise C.WinError(C.get_last_error())
    acquired = False; job = None; child = None
    try:
        if kernel.WaitForSingleObject(mutex, 0) != 0:
            raise RuntimeError('Another supervisor owns this host')
        acquired = True
        stable_since = time.monotonic()
        while time.monotonic() - stable_since < 60:
            ram, commit = telemetry(api, kernel, psapi)
            if ram < ADMISSION_RAM or commit < ADMISSION_COMMIT:
                raise RuntimeError('Admission headroom fell; no job launched')
            time.sleep(0.5)
        if any(name in forbidden for _, name, _ in inventory(kernel)):
            raise RuntimeError('Heavy verification appeared during admission')
        live_cap = effective_commit_cap(0, ram, commit)
        job = owned_job(api, kernel, live_cap)
        kernel.QueryInformationJobObject.argtypes = [W.HANDLE, C.c_int, C.c_void_p, W.DWORD, C.c_void_p]
        child = subprocess.Popen([sys.executable, '-B', str(runner),
                                  '--execute-reviewed-plan-sha256', plan_sha], cwd=root,
                                 creationflags=subprocess.CREATE_NO_WINDOW | 0x4 | subprocess.BELOW_NORMAL_PRIORITY_CLASS,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                 env=dict(os.environ, LEAN_NUM_THREADS='1'))
        if not kernel.AssignProcessToJobObject(job, W.HANDLE(int(child._handle))):
            child.kill(); raise C.WinError(C.get_last_error())
        nt = C.WinDLL('ntdll'); nt.NtResumeProcess.argtypes = [W.HANDLE]
        if nt.NtResumeProcess(W.HANDLE(int(child._handle))) != 0:
            raise RuntimeError('Could not resume owned controller')
        output_errors = []; output_tail = bytearray()
        def capture_output():
            try:
                with (root / 'controller-output.log').open('xb') as stream:
                    total = 0
                    while True:
                        block = child.stdout.read(16384)
                        if not block: break
                        total += len(block)
                        if total > MIB: raise RuntimeError('Controller diagnostic output cap')
                        stream.write(block); stream.flush()
                        output_tail.extend(block)
                        if len(output_tail) > 4096: del output_tail[:-4096]
            except BaseException as error:
                output_errors.append(str(error))
        reader = threading.Thread(target=capture_output, daemon=True); reader.start()
        print(json.dumps({'event': 'owned_controller_started', 'pid': child.pid,
                          'whole_group_commit_max_mib': GROUP_CAP // MIB,
                          'effective_group_commit_cap_mib': live_cap // MIB}), flush=True)
        started = last_report = last_inventory = time.monotonic()
        while child.poll() is None:
            if output_errors: raise RuntimeError(output_errors[0])
            ram, commit = telemetry(api, kernel, psapi)
            if ram < RUNNING_RAM or commit < RUNNING_COMMIT:
                raise RuntimeError('Host headroom pressure; stopping owned job only')
            current_commit = owned_private_commit(api, kernel, psapi, child.pid, job)
            live_cap = effective_commit_cap(current_commit, ram, commit)
            update_owned_job_limit(api, kernel, job, live_cap)
            counters = api.EXTENDED_LIMIT()
            if not kernel.QueryInformationJobObject(job, 9, C.byref(counters), C.sizeof(counters), None):
                raise RuntimeError('Owned-job memory telemetry unavailable')
            if counters.PeakJobMemoryUsed >= GROUP_CAP:
                raise RuntimeError('Owned group memory cap')
            if time.monotonic() - started > 1800:
                raise RuntimeError('Whole-lifecycle wall time cap')
            if time.monotonic() - last_inventory >= 1:
                for _, name, parent in inventory(kernel):
                    if name in forbidden and not (name == 'lean.exe' and parent == child.pid):
                        raise RuntimeError('Other heavy verification appeared; stopping owned job only')
                last_inventory = time.monotonic()
            if time.monotonic() - last_report >= 30:
                print(json.dumps({'event': 'supervisor_heartbeat', 'free_ram_mib': ram // MIB,
                                  'commit_headroom_mib': commit // MIB,
                                  'current_owned_commit_mib': current_commit // MIB,
                                  'effective_group_commit_cap_mib': live_cap // MIB,
                                  'peak_owned_commit_mib': counters.PeakJobMemoryUsed // MIB}), flush=True)
                last_report = time.monotonic()
            time.sleep(0.25)
        reader.join(timeout=5)
        if output_errors: raise RuntimeError(output_errors[0])
        print(json.dumps({'event': 'controller_exited', 'exit_code': child.returncode,
                          'diagnostic_tail': output_tail.decode('utf-8', errors='replace') if child.returncode else '',
                          'proof_status': 'Read exact frozen events; exit code is not qualification'}), flush=True)
    finally:
        if job:
            kernel.TerminateJobObject(job, 1)
            if child is not None: child.wait(timeout=10)
            kernel.CloseHandle(job)
        if acquired: kernel.ReleaseMutex(mutex)
        kernel.CloseHandle(mutex)


if __name__ == '__main__':
    main()
