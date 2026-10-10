"""Owned dummy-process cleanup controls only; no theorem prover is invoked."""
import argparse,ast,hashlib,json,os,subprocess,sys,tempfile,time
from pathlib import Path
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
S=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--inventory',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();inventory=json.loads(args.inventory.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert {p.name for p in S.iterdir()}==set(inventory['maintained_files'])
for name,e in inventory['maintained_files'].items():
    p=S/name;assert p.is_file() and not p.is_symlink() and sha(p)==e['sha256'] and p.stat().st_size==e['bytes']
assert sha(Path(__file__))==inventory['maintained_files'][Path(__file__).name]['sha256']
sys.path.insert(0,str(S))
from owned_process import cleanup_owned
from source_contract import closed
closed(S,inventory,Path(__file__))
# Ensure the production runner's Popen/monitor body is directly protected by a
# finally which calls this exact helper; no test-only alternate runner is used.
tree=ast.parse((S/'build_successors_bounded.py').read_text())
protected=[node for node in ast.walk(tree) if isinstance(node,ast.Try) and node.finalbody and
           any(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='Popen' for part in node.body for n in ast.walk(part)) and
           any(isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='cleanup_owned' for part in node.finalbody for n in ast.walk(part))]
assert protected,'production Popen not protected by owned cleanup finally'
observations=[]
def live_group(pgid):
    text=subprocess.check_output(['ps','-axo','pgid=,stat='],text=True)
    return [line.strip() for line in text.splitlines() if len(p:=line.split())==2 and int(p[0])==pgid and not p[1].startswith('Z')]
for exception in [OSError('injected memory/ps monitor refusal'),KeyboardInterrupt('injected monitor interruption')]:
    proc=None;seen=None
    try:
        proc=subprocess.Popen([sys.executable,'-I','-B','-S','-c','import time; time.sleep(30)'],start_new_session=True)
        raise exception
    except BaseException as error:seen=type(error).__name__
    finally:
        if proc is not None:cleanup=cleanup_owned(proc,.2)
    assert seen==type(exception).__name__ and cleanup['leader_reaped'] and not cleanup['errors'] and not live_group(proc.pid)
    observations.append({'case':seen,'cleanup':cleanup,'live_group_after':False,'proof_credit':0})
# A leader can exit while a child remains in the same owned group.
with tempfile.TemporaryDirectory(prefix='call13-cleanup-controls-') as tmp:
    ready=Path(tmp)/'ready'
    child='import signal,time; signal.signal(signal.SIGTERM,signal.SIG_IGN); open('+repr(str(ready))+',"w").write("ready"); time.sleep(30)'
    leader='import subprocess,sys; subprocess.Popen([sys.executable,"-I","-B","-S","-c",'+repr(child)+'])'
    proc=subprocess.Popen([sys.executable,'-I','-B','-S','-c',leader],start_new_session=True)
    try:
        deadline=time.monotonic()+5
        while not ready.exists() and time.monotonic()<deadline:time.sleep(.02)
        assert ready.exists();assert proc.wait(timeout=5)==0;assert live_group(proc.pid)
    finally:cleanup=cleanup_owned(proc,.2)
    deadline=time.monotonic()+2
    while live_group(proc.pid) and time.monotonic()<deadline:time.sleep(.02)
    assert cleanup['leader_reaped'] and not cleanup['errors'] and 'SIGKILL' in cleanup['signals'] and not live_group(proc.pid)
    observations.append({'case':'exited leader with SIGTERM-resistant child','cleanup':cleanup,'live_group_after':False,'proof_credit':0})
closed(S,inventory,Path(__file__))
result={'status':'passed','schema':'call13-owned-cleanup-controls01','observations':observations,
        'production_finally_bound':True,'executing_recipe_sha256':sha(Path(__file__)),
        'maintained_inventory_sha256':sha(args.inventory),'kernel_runs':0,
        'scope':'dummy owned Python process groups; unexpected monitor exception, interruption, orphan child cleanup. ZERO mathematical proof credit'}
with args.output.open('x') as handle:json.dump(result,handle,indent=2);handle.write('\n')
print(json.dumps({'status':'passed','owned_process_controls':3,'kernel_runs':0}))
