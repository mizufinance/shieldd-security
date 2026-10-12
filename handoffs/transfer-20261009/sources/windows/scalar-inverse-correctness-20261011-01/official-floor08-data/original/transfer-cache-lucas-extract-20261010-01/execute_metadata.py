"""Execute one reviewed metadata command in a kill-on-close monitored job."""
import sys
sys.dont_write_bytecode = True
import argparse
import ctypes as C
from ctypes import wintypes as W
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import threading
import time
ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('guards', ROOT.parent / 'transfer-prerequisite-floor-20261010-06/execute_bounded.py')
guards = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guards)
guards.ROOT = ROOT
def extraction_usage(stable=False):
    total = metadata = 0
    for path in ROOT.rglob('*'):
        if not path.is_file(): continue
        try: size = path.stat().st_size
        except FileNotFoundError:
            if stable: raise
            continue
        total += size
        if path.suffix in ('.json', '.jsonl', '.txt'): metadata += size
    assert total < 64 * 1024**2 and metadata < 16 * 1024**2, 'Artifact cap'
    return total, metadata

parser = argparse.ArgumentParser()
parser.add_argument('--execute-reviewed-plan-sha256', required=True)
args = parser.parse_args()
assert guards.digest(ROOT / 'plan.json') == args.execute_reviewed_plan_sha256
plan = json.loads((ROOT / 'plan.json').read_text())
assert plan['host'] == os.environ['COMPUTERNAME']
assert plan['limits'] == {'seconds': 120, 'active_processes': 2, 'job_memory_bytes': 4 * 1024**3,
    'output_bytes': 1024**2, 'all_new_bytes': 64 * 1024**2, 'metadata_bytes': 16 * 1024**2}
assert plan['modules'] == ['Mathlib.NumberTheory.LucasPrimality']
assert plan['command'][1:5] == ['--jobs', '1', '-x', '-C']
assert plan['command'][5] == str(ROOT / 'extracted')
assert plan['command'][6:] == [p['path'] for p in plan['archives']]
assert Path(plan['command'][0]).name == 'leantar.exe'
guards.verify(plan['pins'])
assert not (ROOT / 'result.json').exists() and not (ROOT / 'stdout.txt').exists(), 'No reset/retry'
kernel, psapi = guards.winapi()
mutex = kernel.CreateMutexW(None, False, 'Global\\ShielddFormalHeavyVerification')
assert mutex and kernel.WaitForSingleObject(mutex, 0) == 0, 'Host verification mutex busy'
class ENTRY(C.Structure):
    _fields_ = [('dwSize', W.DWORD), ('cntUsage', W.DWORD), ('th32ProcessID', W.DWORD),
        ('th32DefaultHeapID', C.c_size_t), ('th32ModuleID', W.DWORD), ('cntThreads', W.DWORD),
        ('th32ParentProcessID', W.DWORD), ('pcPriClassBase', W.LONG), ('dwFlags', W.DWORD), ('szExeFile', W.WCHAR * 260)]
kernel.CreateToolhelp32Snapshot.argtypes = [W.DWORD, W.DWORD]
kernel.CreateToolhelp32Snapshot.restype = W.HANDLE
kernel.Process32FirstW.argtypes = [W.HANDLE, C.POINTER(ENTRY)]
kernel.Process32NextW.argtypes = [W.HANDLE, C.POINTER(ENTRY)]
job = None
process = None
started = time.monotonic()
collected = bytearray()
errors = []
try:
    snap = kernel.CreateToolhelp32Snapshot(2, 0)
    assert snap != C.c_void_p(-1).value
    try:
        entry = ENTRY(); entry.dwSize = C.sizeof(entry)
        ok = kernel.Process32FirstW(snap, C.byref(entry)); assert ok
        while ok:
            assert entry.szExeFile.lower() not in ('lean.exe', 'lake.exe', 'cargo.exe', 'rustc.exe', 'cache.exe', 'leantar.exe', 'quint.exe', 'tlc.exe'), entry.szExeFile
            ok = kernel.Process32NextW(snap, C.byref(entry))
    finally: kernel.CloseHandle(snap)
    guards.pressure(kernel, psapi, True)
    job = kernel.CreateJobObjectW(None, None); assert job
    limits = guards.EXTENDED_LIMIT()
    limits.Basic.LimitFlags = 0x2000 | 0x200 | 0x8
    limits.Basic.ActiveProcessLimit = 2
    limits.JobMemoryLimit = 4 * 1024**3
    assert kernel.SetInformationJobObject(job, 9, C.byref(limits), C.sizeof(limits))
    env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_SRC_PATH=';'.join(plan['source_path']),
        MATHLIB_CACHE_DIR=plan['cache_dir'], PATH=plan['toolchain_bin'] + ';' + os.environ['PATH'])
    process = subprocess.Popen(plan['command'], cwd=plan['cwd'], env=env,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        creationflags=subprocess.CREATE_NO_WINDOW | 0x4)
    assert kernel.AssignProcessToJobObject(job, W.HANDLE(int(process._handle)))
    nt = C.WinDLL('ntdll'); nt.NtResumeProcess.argtypes = [W.HANDLE]
    assert nt.NtResumeProcess(W.HANDLE(int(process._handle))) == 0
    def read():
        try:
            with (ROOT / 'stdout.txt').open('xb') as stream:
                while True:
                    data = process.stdout.read(16384)
                    if not data: break
                    assert len(collected) + len(data) <= 1024**2
                    stream.write(data); stream.flush(); collected.extend(data)
        except BaseException as e: errors.append(str(e))
    reader = threading.Thread(target=read, daemon=True); reader.start()
    while process.poll() is None:
        guards.pressure(kernel, psapi, False)
        extraction_usage()
        assert time.monotonic() - started < 120, 'Metadata timeout'
        assert not errors, errors
        time.sleep(0.2)
    reader.join(5); assert not reader.is_alive() and not errors
    assert process.returncode == 0, 'Metadata command exit ' + str(process.returncode)
    guards.verify(plan['pins'])
    guards.pressure(kernel, psapi, False)
    total, metadata = extraction_usage(stable=True)
    status = {'all_new_bytes': total, 'metadata_bytes': metadata, 'status': 'passed', 'seconds': time.monotonic() - started,
        'stdout_bytes': len(collected), 'stdout_sha256': guards.digest(ROOT / 'stdout.txt'), 'credit': 0}
except BaseException as e:
    status = {'status': 'failed', 'reason': str(e), 'seconds': time.monotonic() - started, 'credit': 0}
finally:
    if process is not None and process.poll() is None:
        if job: kernel.TerminateJobObject(job, 1)
        else: process.kill()
        process.wait(timeout=10)
    if job: kernel.CloseHandle(job)
    kernel.ReleaseMutex(mutex); kernel.CloseHandle(mutex)
(ROOT / 'result.json').write_text(json.dumps(status, indent=2) + '\n')
print(json.dumps(status))
