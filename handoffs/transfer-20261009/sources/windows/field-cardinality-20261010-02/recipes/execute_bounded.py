"""One Windows host, one named Lean process; prepared plan must be reviewed first.

No implicit builds, downloads, cache writes, old-controller calls, or retries.
Run only with --execute-reviewed-plan-sha256 <the reviewed plan.json digest>.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import ctypes as C
from ctypes import wintypes as W
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parent
ALL_CAP, META_CAP = 64 * 1024**2, 16 * 1024**2
LOG_CAP, OBJECT_CAP = 1024**2, 4 * 1024**2
ATTEMPTS, SECONDS = 8, 600


def digest(path):
    with Path(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def verify(records):
    for item in records:
        path = Path(item['path'])
        if path.stat().st_size != item['bytes'] or digest(path) != item['sha256']:
            raise RuntimeError('Immutable input changed: ' + str(path))


def usage():
    files = [p for p in ROOT.rglob('*') if p.is_file()]
    total = sum(p.stat().st_size for p in files)
    metadata = sum(p.stat().st_size for p in files if p.suffix in ('.json', '.jsonl', '.txt'))
    if total >= ALL_CAP or metadata >= META_CAP:
        raise RuntimeError('Fresh-task artifact/metadata guard')
    return total, metadata


def event(item):
    data = (json.dumps(item, sort_keys=True) + '\n').encode()
    total, metadata = usage()
    if total + len(data) >= ALL_CAP or metadata + len(data) >= META_CAP:
        raise RuntimeError('Ledger reservation exceeds task byte cap')
    with (ROOT / 'events.jsonl').open('ab') as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())


class MEMORYSTATUSEX(C.Structure):
    _fields_ = [('length', W.DWORD), ('load', W.DWORD)] + [(n, C.c_ulonglong) for n in
        ('totalPhys', 'availPhys', 'totalPage', 'availPage', 'totalVirtual', 'availVirtual', 'extended')]


class PERFORMANCE_INFORMATION(C.Structure):
    _fields_ = [('cb', W.DWORD)] + [(n, C.c_size_t) for n in
        ('CommitTotal', 'CommitLimit', 'CommitPeak', 'PhysicalTotal', 'PhysicalAvailable',
         'SystemCache', 'KernelTotal', 'KernelPaged', 'KernelNonpaged', 'PageSize')] + [
        ('HandleCount', W.DWORD), ('ProcessCount', W.DWORD), ('ThreadCount', W.DWORD)]


class PROCESS_MEMORY_COUNTERS(C.Structure):
    _fields_ = [('cb', W.DWORD), ('PageFaultCount', W.DWORD)] + [(n, C.c_size_t) for n in
        ('PeakWorkingSetSize', 'WorkingSetSize', 'QuotaPeakPagedPoolUsage', 'QuotaPagedPoolUsage',
         'QuotaPeakNonPagedPoolUsage', 'QuotaNonPagedPoolUsage', 'PagefileUsage', 'PeakPagefileUsage')]


class IO_COUNTERS(C.Structure):
    _fields_ = [(n, C.c_ulonglong) for n in ('ReadOperationCount', 'WriteOperationCount',
        'OtherOperationCount', 'ReadTransferCount', 'WriteTransferCount', 'OtherTransferCount')]


class BASIC_LIMIT(C.Structure):
    _fields_ = [('ProcessTime', C.c_longlong), ('JobTime', C.c_longlong), ('LimitFlags', W.DWORD),
        ('MinWorkingSet', C.c_size_t), ('MaxWorkingSet', C.c_size_t), ('ActiveProcessLimit', W.DWORD),
        ('Affinity', C.c_size_t), ('PriorityClass', W.DWORD), ('SchedulingClass', W.DWORD)]


class EXTENDED_LIMIT(C.Structure):
    _fields_ = [('Basic', BASIC_LIMIT), ('IO', IO_COUNTERS), ('ProcessMemoryLimit', C.c_size_t),
        ('JobMemoryLimit', C.c_size_t), ('PeakProcessMemoryUsed', C.c_size_t), ('PeakJobMemoryUsed', C.c_size_t)]


def winapi():
    kernel = C.WinDLL('kernel32', use_last_error=True)
    psapi = C.WinDLL('psapi', use_last_error=True)
    kernel.CreateJobObjectW.argtypes = [C.c_void_p, W.LPCWSTR]
    kernel.CreateJobObjectW.restype = W.HANDLE
    kernel.SetInformationJobObject.argtypes = [W.HANDLE, C.c_int, C.c_void_p, W.DWORD]
    kernel.AssignProcessToJobObject.argtypes = [W.HANDLE, W.HANDLE]
    kernel.TerminateJobObject.argtypes = [W.HANDLE, W.UINT]
    kernel.CloseHandle.argtypes = [W.HANDLE]
    kernel.CreateMutexW.argtypes = [C.c_void_p, W.BOOL, W.LPCWSTR]
    kernel.CreateMutexW.restype = W.HANDLE
    kernel.WaitForSingleObject.argtypes = [W.HANDLE, W.DWORD]
    kernel.ReleaseMutex.argtypes = [W.HANDLE]
    kernel.GlobalMemoryStatusEx.argtypes = [C.POINTER(MEMORYSTATUSEX)]
    psapi.GetPerformanceInfo.argtypes = [C.POINTER(PERFORMANCE_INFORMATION), W.DWORD]
    psapi.GetProcessMemoryInfo.argtypes = [W.HANDLE, C.POINTER(PROCESS_MEMORY_COUNTERS), W.DWORD]
    return kernel, psapi


def pressure(kernel, psapi, starting):
    mem = MEMORYSTATUSEX(); mem.length = C.sizeof(mem)
    perf = PERFORMANCE_INFORMATION(); perf.cb = C.sizeof(perf)
    if not kernel.GlobalMemoryStatusEx(C.byref(mem)) or not psapi.GetPerformanceInfo(C.byref(perf), perf.cb):
        raise RuntimeError('Physical/commit memory telemetry unavailable')
    commit = (perf.CommitLimit - perf.CommitTotal) * perf.PageSize
    if mem.availPhys < (2560 if starting else 1536) * 1024**2:
        raise RuntimeError('Physical memory pressure')
    if commit < (1792 if starting else 512) * 1024**2:
        raise RuntimeError('Commit headroom pressure')
    if shutil.disk_usage(ROOT).free < 2 * 1024**3:
        raise RuntimeError('Free disk pressure')


def audit(text, names):
    if re.search(r'\b(?:error|warning|info|trace):|\bsorryAx\b|declaration uses .sorry.', text):
        raise RuntimeError('Lean error/placeholder output')
    reports = list(re.finditer(r"(?m)^'([^']+)' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)", text))
    if [report.group(1) for report in reports] != names:
        raise RuntimeError('Unexpected, duplicate, missing, or reordered axiom diagnostics')
    result = {}; cursor = 0
    for name in names:
        pattern = r"(?m)^@?" + re.escape(name) + r"\s*:[\s\S]*?^'" + re.escape(name) + r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
        matches = list(re.finditer(pattern, text))
        if len(matches) != 1:
            raise RuntimeError('Missing/duplicate full type and axiom pair: ' + name)
        if text[cursor:matches[0].start()].strip():
            raise RuntimeError('Unexplained compiler output before: ' + name)
        cursor = matches[0].end()
        axioms = [v.strip() for v in (matches[0].group(1) or '').split(',') if v.strip()]
        if not set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}:
            raise RuntimeError('Unexpected axiom: ' + name)
        signature = matches[0].group(0).split("\n'" + name + "' ", 1)[0]
        if any(line.strip() and not line[0].isspace() for line in signature.splitlines()[1:]):
            raise RuntimeError('Unexplained unindented output within full type: ' + name)
        result[name] = {'full_type_sha256': hashlib.sha256(signature.encode()).hexdigest(), 'axioms': axioms}
    if text[cursor:].strip(): raise RuntimeError('Unexplained compiler output after final audit')
    return result


def code_only(text):
    out = []; i = 0; depth = 0; line = False; string = False
    while i < len(text):
        pair, char = text[i:i+2], text[i]
        if line:
            out.append('\n' if char == '\n' else ' ')
            if char == '\n': line = False
            i += 1
        elif depth:
            if pair == '/-': depth += 1; out.extend('  '); i += 2
            elif pair == '-/': depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if char == '\n' else ' '); i += 1
        elif string:
            if char == '\\' and i + 1 < len(text): out.extend('  '); i += 2
            else:
                if char == '"': string = False
                out.append('\n' if char == '\n' else ' '); i += 1
        elif pair == '--': line = True; out.extend('  '); i += 2
        elif pair == '/-': depth = 1; out.extend('  '); i += 2
        elif char == '"': string = True; out.append(' '); i += 1
        else: out.append(char); i += 1
    # Only the header before the first declaration is consumed below. Body
    # character literals can contain quotes; their masking cannot affect the
    # already produced header prefix and is not a body-parsing claim.
    return ''.join(out)

def header(text):
    imports = []; prelude = False
    for line in code_only(text).splitlines():
        line = line.strip()
        if not line or line == 'module': continue
        if line == 'prelude': prelude = True; continue
        match = re.fullmatch(r'(?:(?:public|private|protected|meta)\s+)*import(?:\s+all)?\s+(.+)', line)
        if not match: break
        names = match.group(1).split()
        assert all(re.fullmatch(r'[A-Za-z0-9_.]+', n) for n in names), line
        imports.extend(names)
    return imports, not prelude

def own_cache(accepted_objects):
    project = ROOT / 'project' / 'ShielddSecurity'
    expected = {os.path.normcase(str(Path(t['source']['path']).resolve())) for t in PLAN['targets']}
    expected.update(os.path.normcase(str(Path(p['path']).resolve())) for p in accepted_objects)
    actual = set()
    for path in project.rglob('*'):
        if path.is_file():
            if path.is_symlink() or project.resolve() not in path.resolve().parents:
                raise RuntimeError('Unexpected linked/escaped own-cache input')
            actual.add(os.path.normcase(str(path.resolve())))
    if actual != expected:
        raise RuntimeError('Own cache keyset changed; future/unqualified artifacts are forbidden')
    verify(accepted_objects)


def import_resolution(floor, target=None, accepted_objects=()):
    # Lean/Util/Path.lean findWithExt chooses the first PACKAGE root, not first module hit.
    search = [Path(p) for p in PLAN['lean_path']] + [Path(PLAN['lean']['path']).parent.parent / 'lib' / 'lean']
    def selected(module):
        package = module.split('.')[0]
        root = next((p for p in search if (p / package).is_dir() or (p / (package + '.olean')).exists()), None)
        if root is None: raise RuntimeError('No first package root: ' + module)
        return root / (module.replace('.', '/') + '.olean')
    for module, item in floor['modules'].items():
        expected = next((p for p in item['objects'] if p['path'].endswith('.olean')), None)
        if expected is None or selected(module).resolve() != Path(expected['path']).resolve():
            raise RuntimeError('First package root shadows external import: ' + module)
    if target is not None:
        actual_imports, implicit_init = header(Path(target['source']['path']).read_text(encoding='utf-8'))
        if actual_imports != target['imports']:
            raise RuntimeError('Planned imports differ from actual source header')
        if implicit_init and 'Init' not in floor['modules']:
            raise RuntimeError('Implicit Init missing from pinned external floor')
        accepted = {os.path.normcase(str(Path(p['path']).resolve())) for p in accepted_objects}
        for module in target['imports']:
            path = selected(module)
            if module.startswith('ShielddSecurity.') and os.path.normcase(str(path.resolve())) not in accepted:
                raise RuntimeError('Unqualified or omitted owned import: ' + module)
            if not module.startswith('ShielddSecurity.') and module not in floor['modules']:
                raise RuntimeError('Direct external import absent from pinned floor: ' + module)
            if not path.is_file(): raise RuntimeError('First package root has no import object: ' + module)


def run_target(kernel, psapi, target, attempt, remaining):
    output = ROOT / 'runs' / ('%02d-%s' % (attempt, target['module']))
    output.mkdir(parents=True, exist_ok=False)
    pressure(kernel, psapi, True)
    total, _ = usage()
    if total + 6 * OBJECT_CAP + LOG_CAP + 256 * 1024 >= ALL_CAP:
        raise RuntimeError('Conservative output reservation exceeds task byte cap')
    source = Path(target['source']['path'])
    command = [PLAN['lean']['path'], '-j1', '-M1536', '-DmaxHeartbeats=300000',
        '-DmaxRecDepth=4096', '-o', str(ROOT / 'project' / 'ShielddSecurity' / (target['module'] + '.olean')),
        str(source)]
    job = kernel.CreateJobObjectW(None, None)
    if not job: raise C.WinError(C.get_last_error())
    limits = EXTENDED_LIMIT()
    limits.Basic.LimitFlags = 0x2000 | 0x200 | 0x8  # Kill on close, job memory, one active process.
    limits.Basic.ActiveProcessLimit = 1
    limits.JobMemoryLimit = 4 * 1024**3
    if not kernel.SetInformationJobObject(job, 9, C.byref(limits), C.sizeof(limits)):
        kernel.CloseHandle(job); raise C.WinError(C.get_last_error())
    environment = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=';'.join(PLAN['lean_path']))
    process = None; started = time.monotonic(); stopped = threading.Event(); reason = None
    peak = 0; collected = bytearray(); reader_error = []
    try:
        process = subprocess.Popen(command, cwd=ROOT / 'project', env=environment,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            creationflags=subprocess.CREATE_NO_WINDOW | 0x4)  # Assign suspended, then resume.
        if not kernel.AssignProcessToJobObject(job, W.HANDLE(int(process._handle))):
            process.kill(); raise C.WinError(C.get_last_error())
        nt = C.WinDLL('ntdll'); nt.NtResumeProcess.argtypes = [W.HANDLE]
        if nt.NtResumeProcess(W.HANDLE(int(process._handle))) != 0:
            raise RuntimeError('Could not resume owned Lean process')
        def read_output():
            try:
                with (output / 'stdout.txt').open('xb') as stream:
                    while True:
                        data = process.stdout.read(16384)
                        if not data: break
                        if len(collected) + len(data) > LOG_CAP:
                            raise RuntimeError('Per-attempt output cap')
                        total, _ = usage()
                        if total + len(data) >= ALL_CAP:
                            raise RuntimeError('Fresh-task artifact cap')
                        stream.write(data); stream.flush(); collected.extend(data)
            except BaseException as error:
                reader_error.append(str(error)); stopped.set()
        reader = threading.Thread(target=read_output, daemon=True); reader.start()
        while process.poll() is None:
            pressure(kernel, psapi, False)
            counters = PROCESS_MEMORY_COUNTERS(); counters.cb = C.sizeof(counters)
            if not psapi.GetProcessMemoryInfo(W.HANDLE(int(process._handle)), C.byref(counters), counters.cb):
                raise RuntimeError('Owned-process RSS telemetry unavailable')
            peak = max(peak, counters.WorkingSetSize)
            if peak > 4 * 1024**3: raise RuntimeError('Owned-process RSS cap')
            if time.monotonic() - started >= min(240, remaining): raise RuntimeError('Lean elapsed-time cap')
            if stopped.is_set(): raise RuntimeError(reader_error[0])
            usage()
            artifacts = list((ROOT / 'project' / 'ShielddSecurity').glob(target['module'] + '.*'))
            if len([p for p in artifacts if p.suffix != '.lean']) > 6:
                raise RuntimeError('Unexpected named-module output count')
            for artifact in artifacts:
                if artifact.suffix != '.lean' and artifact.stat().st_size > OBJECT_CAP:
                    raise RuntimeError('Per-artifact output cap')
            time.sleep(0.2)
        reader.join(timeout=5)
        if reader.is_alive() or reader_error: raise RuntimeError('Output reader incomplete: ' + str(reader_error))
        if process.returncode != 0: raise RuntimeError('Lean exit ' + str(process.returncode))
        pressure(kernel, psapi, False)
        if time.monotonic() - started > min(240, remaining): raise RuntimeError('Post-exit Lean elapsed-time cap')
        if len(collected) > LOG_CAP: raise RuntimeError('Post-exit output cap')
        evidence = audit(collected.decode('utf-8', errors='strict'), target['audit_names'])
        objects = [{'path': str(p), 'bytes': p.stat().st_size, 'sha256': digest(p)}
            for p in (ROOT / 'project' / 'ShielddSecurity').glob(target['module'] + '.*') if p.suffix != '.lean']
        usage()
        if len(objects) > 6: raise RuntimeError('Post-exit named-module output count')
        if any(Path(p['path']).name[len(target['module']):] not in
            ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir') for p in objects):
            raise RuntimeError('Unexpected post-exit named-module artifact')
        if any(p['bytes'] > OBJECT_CAP for p in objects): raise RuntimeError('Per-artifact output cap')
        if not any(p['path'].endswith('.olean') for p in objects): raise RuntimeError('Missing output object')
        stdout_record = {'path': str(output / 'stdout.txt'), 'bytes': len(collected), 'sha256': digest(output / 'stdout.txt')}
        pressure(kernel, psapi, False)
        final_elapsed = time.monotonic() - started
        if final_elapsed > min(240, remaining): raise RuntimeError('Final Lean elapsed-time cap')
        return {'status': 'passed', 'seconds': final_elapsed, 'peak_rss_bytes': peak,
                'command': command, 'objects': objects, 'audits': evidence,
                'stdout': stdout_record}
    finally:
        if process is not None and process.poll() is None:
            kernel.TerminateJobObject(job, 1)
            process.wait(timeout=10)
        kernel.CloseHandle(job)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--execute-reviewed-plan-sha256', required=True)
    args = parser.parse_args()
    if os.name != 'nt': raise SystemExit('Pinned Windows host only')
    if digest(ROOT / 'plan.json') != args.execute_reviewed_plan_sha256:
        raise SystemExit('Reviewed plan hash mismatch')
    PLAN = json.loads((ROOT / 'plan.json').read_text())
    if PLAN['limits'] != {'attempts': 8, 'lean_seconds': 600, 'heap_mib': 1536, 'threads': 1,
        'max_heartbeats': 300000, 'max_rec_depth': 4096, 'all_bytes': ALL_CAP, 'metadata_bytes': META_CAP}:
        raise SystemExit('Fixed task limits changed')
    if not PLAN['external_floor']['admission_ready']: raise SystemExit('External import floor unresolved')
    if PLAN['host'] != os.environ.get('COMPUTERNAME'): raise SystemExit('Physical host mismatch')
    records = PLAN['pins'] + [t['source'] for t in PLAN['targets']]
    floor = json.loads(Path(PLAN['external_floor']['path']).read_text())
    import_resolution(floor)
    records += floor['immutable_files']
    verify(records)
    previous = [json.loads(line) for line in (ROOT / 'events.jsonl').read_text().splitlines()] if (ROOT / 'events.jsonl').exists() else []
    starts = [e for e in previous if e['event'] == 'attempt_started']
    finishes = [e for e in previous if e['event'] == 'attempt_finished']
    if len(starts) != len(finishes): raise SystemExit('Unfinished attempt retained; no reset/resume')
    if any(e['result']['status'] != 'passed' for e in finishes): raise SystemExit('Failed attempt retained; no automatic retry')
    accepted_objects = PLAN['owned_imports'] + [p for e in finishes for p in e['result'].get('objects', [])]
    records += accepted_objects + [e['result']['stdout'] for e in finishes]
    own_cache(accepted_objects)
    elapsed = sum(e['result']['seconds'] for e in finishes)
    kernel, psapi = winapi()
    mutex = kernel.CreateMutexW(None, False, 'Global\\ShielddFormalHeavyVerification')
    if not mutex or kernel.WaitForSingleObject(mutex, 0) != 0:
        raise SystemExit('Another host verification owns the mutex')
    try:
        # Windows process inventory is read directly; no helper or Lake process.
        class PROCESSENTRY32W(C.Structure):
            _fields_ = [('dwSize', W.DWORD), ('cntUsage', W.DWORD), ('th32ProcessID', W.DWORD),
                ('th32DefaultHeapID', C.c_size_t), ('th32ModuleID', W.DWORD), ('cntThreads', W.DWORD),
                ('th32ParentProcessID', W.DWORD), ('pcPriClassBase', W.LONG), ('dwFlags', W.DWORD),
                ('szExeFile', W.WCHAR * 260)]
        kernel.CreateToolhelp32Snapshot.argtypes = [W.DWORD, W.DWORD]; kernel.CreateToolhelp32Snapshot.restype = W.HANDLE
        kernel.Process32FirstW.argtypes = [W.HANDLE, C.POINTER(PROCESSENTRY32W)]
        kernel.Process32NextW.argtypes = [W.HANDLE, C.POINTER(PROCESSENTRY32W)]
        snapshot = kernel.CreateToolhelp32Snapshot(2, 0)
        if snapshot == C.c_void_p(-1).value:
            raise RuntimeError('Host process inventory unavailable')
        entry = PROCESSENTRY32W(); entry.dwSize = C.sizeof(entry)
        try:
            ok = kernel.Process32FirstW(snapshot, C.byref(entry))
            if not ok: raise RuntimeError('Host process inventory unavailable')
            while ok:
                if entry.szExeFile.lower() in ('lean.exe', 'lake.exe', 'cargo.exe', 'rustc.exe', 'quint.exe', 'tlc.exe'):
                    raise RuntimeError('Existing heavy verification process: ' + entry.szExeFile)
                ok = kernel.Process32NextW(snapshot, C.byref(entry))
        finally: kernel.CloseHandle(snapshot)
        for index, target in enumerate(PLAN['targets'][len(starts):], len(starts) + 1):
            if index > ATTEMPTS or elapsed >= SECONDS: break
            event({'event': 'attempt_started', 'attempt': index, 'module': target['module'], 'utc_epoch': time.time()})
            began = time.monotonic()
            try:
                own_cache(accepted_objects)
                import_resolution(floor, target, accepted_objects)
                verify(records)
                result = run_target(kernel, psapi, target, index, SECONDS - elapsed)
                accepted_objects += result['objects']
                own_cache(accepted_objects)
                records += result['objects']
                records.append(result['stdout'])
                verify(records)
            except BaseException as error:
                result = {'status': 'failed', 'reason': str(error), 'seconds': time.monotonic() - began}
            elapsed += result['seconds']
            event({'event': 'attempt_finished', 'attempt': index, 'module': target['module'], 'result': result})
            if result['status'] != 'passed': break
    finally:
        kernel.ReleaseMutex(mutex); kernel.CloseHandle(mutex)
