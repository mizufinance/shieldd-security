"""Tiny Python process containment check; no Lean, Cargo or proof credit."""
import ctypes as C
from ctypes import wintypes as W
import importlib.util
import json
from pathlib import Path
import queue
import subprocess
import sys
import threading

sys.dont_write_bytecode = True
D = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('supervisor', D / 'supervise-native-verifier-20261014.py')
supervisor = importlib.util.module_from_spec(spec); spec.loader.exec_module(supervisor)
runner = D / 'transfer-blst-arm-inverse-exact-gcd-20261013-01' / 'execute_bounded.py'
assert supervisor.digest(runner) == supervisor.RUNNER_SHA
spec = importlib.util.spec_from_file_location('runner', runner)
api = importlib.util.module_from_spec(spec); spec.loader.exec_module(api)
kernel, psapi = api.winapi()
kernel.OpenProcess.argtypes = [W.DWORD, W.BOOL, W.DWORD]
kernel.OpenProcess.restype = W.HANDLE
kernel.IsProcessInJob.argtypes = [W.HANDLE, W.HANDLE, C.POINTER(W.BOOL)]
kernel.QueryInformationJobObject.argtypes = [W.HANDLE, C.c_int, C.c_void_p, W.DWORD, C.c_void_p]
job = supervisor.owned_job(api, kernel, 128 * supervisor.MIB)
child = descendant_handle = None
code = '''import ctypes as C,importlib.util,json,subprocess,sys,time
from ctypes import wintypes as W
sys.dont_write_bytecode=True
s=importlib.util.spec_from_file_location('r',sys.argv[1]);r=importlib.util.module_from_spec(s);s.loader.exec_module(r)
k,p=r.winapi();j=k.CreateJobObjectW(None,None);assert j
l=r.EXTENDED_LIMIT();l.Basic.LimitFlags=0x2000|0x200|0x8;l.Basic.ActiveProcessLimit=1;l.JobMemoryLimit=64*1024**2
assert k.SetInformationJobObject(j,9,C.byref(l),C.sizeof(l))
c=subprocess.Popen([sys.executable,'-B','-c','import time;time.sleep(20)'],creationflags=subprocess.CREATE_NO_WINDOW|4)
assert k.AssignProcessToJobObject(j,W.HANDLE(int(c._handle)))
n=C.WinDLL('ntdll');n.NtResumeProcess.argtypes=[W.HANDLE];assert n.NtResumeProcess(W.HANDLE(int(c._handle)))==0
print(json.dumps({'descendant_pid':c.pid,'nested_job_assigned':True}),flush=True)
time.sleep(20)
'''
try:
    child = subprocess.Popen([sys.executable, '-B', '-c', code, str(runner)],
                             creationflags=subprocess.CREATE_NO_WINDOW | 4,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    assert kernel.AssignProcessToJobObject(job, W.HANDLE(int(child._handle)))
    nt = C.WinDLL('ntdll'); nt.NtResumeProcess.argtypes = [W.HANDLE]
    assert nt.NtResumeProcess(W.HANDLE(int(child._handle))) == 0
    output = queue.Queue()
    threading.Thread(target=lambda: output.put(child.stdout.readline()), daemon=True).start()
    report = json.loads(output.get(timeout=5))
    descendant_handle = kernel.OpenProcess(0x100000 | 0x1000, False, report['descendant_pid'])
    assert descendant_handle
    for handle in (W.HANDLE(int(child._handle)), descendant_handle):
        belongs = W.BOOL()
        assert kernel.IsProcessInJob(handle, job, C.byref(belongs)) and belongs.value
    counters = api.EXTENDED_LIMIT()
    assert kernel.QueryInformationJobObject(job, 9, C.byref(counters), C.sizeof(counters), None)
    assert 0 < counters.PeakJobMemoryUsed < 128 * supervisor.MIB
    assert kernel.TerminateJobObject(job, 1)
    child.wait(timeout=5)
    assert kernel.WaitForSingleObject(descendant_handle, 5000) == 0
    print(json.dumps({'status': 'passed', 'nested_job_containment': True,
                      'owned_controller_and_descendant_stopped': True,
                      'peak_owned_commit_mib': counters.PeakJobMemoryUsed // supervisor.MIB,
                      'lean_started': False, 'proof_credit': 0}))
finally:
    kernel.TerminateJobObject(job, 1)
    if child is not None:
        if child.poll() is None: child.kill()
        child.wait(timeout=5)
    if descendant_handle: kernel.CloseHandle(descendant_handle)
    kernel.CloseHandle(job)
