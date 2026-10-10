"""EXTERNAL source-only proposal: no launch without parent approved exact config.
Wait for independently issued per-ordinal admissions; never issue or rewrite one.
"""
import argparse,fcntl,hashlib,json,math,os,signal,subprocess,sys,time
from pathlib import Path
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
M=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=argparse.ArgumentParser()
for n in ['config','inventory']:p.add_argument('--'+n,type=Path,required=True)
for n in ['config-sha256','inventory-sha256']:p.add_argument('--'+n,required=True)
a=p.parse_args();assert sha(a.config)==a.config_sha256 and sha(a.inventory)==a.inventory_sha256
mi=json.loads(a.inventory.read_text())
assert {q.name for q in M.iterdir()}==set(mi['maintained_files'])
for n,e in mi['maintained_files'].items():q=M/n;assert q.is_file() and not q.is_symlink() and sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
assert sha(Path(__file__))==mi['maintained_files'][Path(__file__).name]['sha256']
sys.path.insert(0,str(M))
from contract import bounded_json,closed,exact_dispatch,current_state,object_freshness,checked_result
from audit_log import validate
from startup_guard import StartupGuard,CATCHABLE
from owned_runner import OwnedRunner
from continuation_context import load_context,verify_sources,source_path,receipt_name,aggregate_budget,runtime_metadata_size
cfg=bounded_json(a.config,262144)
assert cfg['schema']=='parent-Call14-finaltwo06' and cfg['start_ordinal']==59 and cfg['end_ordinal']==60
assert cfg['controller_sha256']==sha(Path(__file__))
R=Path(cfg['root']);Q=Path(cfg['stage']);D=Path(cfg['dispatch_directory'])
assert all(q.is_absolute() and q.is_dir() and not q.is_symlink() for q in [R,Q,D])
assert Q==R/'work/mac-poseidon-call1-plan14/final-two-control-candidate06'
assert D==R/'work/mac-poseidon-call1-plan14/parent-finaltwo-dispatch06'
assert sha(Path(cfg['feeder_path']))==cfg['feeder_sha256']
approval=bounded_json(Path(cfg['context_approval']),16384)
assert approval['approved'] is True and approval['config_sha256']==a.config_sha256,'separate external parent execution approval required'
assert cfg['limits']=={'attempts':60,'seconds':1200,'source_and_object_bytes':536870912,'includes_two_actual_probes':True,'permodule_seconds':240,'group_RSS':4294967296,'heap_MiB':2048,'jobs':1,'LEAN_NUM_THREADS':1,'memory_free_percent':15,'disk_free_bytes':2147483648,'heartbeats':900000,'recdepth':8192}
si=bounded_json(Q/'source-inventory06.json',4*1024**2);runner_inventory=bounded_json(Q/'maintained-inventory06.json',131072)
source_pin=sha(Q/'source-inventory06.json');runner_pin=sha(Q/'maintained-inventory06.json')
assert source_pin==cfg['source_inventory_sha256']
assert runner_pin==cfg['runner_inventory_sha256']
context=load_context(Path(si['continuation_context_file']),si['continuation_context_sha256'])
assert len(si['full_topological_order'])==58
names=si['full_topological_order'];remaining=si['successor_topological_order'];assert len(remaining)==2 and remaining==context['future_names']
workspace=Path(si['execution_paths']['workspace']);receipts=R/si['prior_receipt_directory'];ledger=R/si['overall_ledger_directory']
initial=Path(cfg['initial_parent_anchor']);assert sha(initial)==cfg['initial_parent_anchor_sha256']=='7b55da60e1fcd1b9309a1bf13be592e24d909336cab4bcdc2e089e7a161eb386'
anchor=bounded_json(initial,131072);previous=anchor['state'];assert previous['launch_intents']==58 and previous==context['initial_state']
assert current_state(ledger,receipts,si['ledger_genesis_sha256'],context)==previous
assert cfg['canonical_head']=='a1962598ad440af95b0237697c7ee6bcc4226fbd' and cfg['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
# Parent creates admissions/observations itself. Worker does not create/issue them.
# A unique controller output directory is the consumed controller claim. Its
# presence prevents restart/reset; no future module launch is self-authorized.
O=D/'controller-observations01';O.mkdir();lockfd=os.open(O/'controller.lock',os.O_CREAT|os.O_EXCL|os.O_RDWR,0o600);fcntl.flock(lockfd,fcntl.LOCK_EX|fcntl.LOCK_NB)
started=time.monotonic();proc=None;tracker=None;guard=StartupGuard();report={'status':'running','actual_modules_invoked':[],'config_sha256':a.config_sha256,'parent_anchor_sha256':sha(initial),'initial_state':previous}
def metadata_size():
 total=runtime_metadata_size(context)
 for n in []:# centralized retained-old+new metadata accounting
  pass
 for n in ['admissions','observations','controller-observations01']:
  sub=D/n
  if not sub.exists():continue
  assert sub.is_dir() and not sub.is_symlink()
  for q in sub.iterdir():
   assert q.is_file() and not q.is_symlink(),'flat bounded metadata directory required'
   # Files already included by runtime_metadata_size(context).
 assert total<=16*1024**2,'combined dispatch metadata/admissions/observations16MiB bound'
 return total
def record(name,value):
 data=(json.dumps(value,indent=2)+'\n').encode();assert len(data)<=131072 and metadata_size()+len(data)<=16*1024**2
 fd=os.open(O/name,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600)
 with os.fdopen(fd,'wb') as f:f.write(data);f.flush();os.fsync(f.fileno())
def identities():
 assert sha(a.config)==a.config_sha256 and sha(a.inventory)==a.inventory_sha256
 closed(M,mi,Path(__file__));closed(Q/'maintained',runner_inventory,Q/'maintained/build_successor_bounded.py')
 assert sha(Path(cfg['feeder_path']))==cfg['feeder_sha256'] and sha(Q/'source-inventory06.json')==source_pin and sha(Q/'maintained-inventory06.json')==runner_pin
 assert bounded_json(Path(cfg['context_approval']),16384)==approval
 for n,e in cfg['reviewed_static_records'].items():q=Path(n);assert q.is_file() and not q.is_symlink() and sha(q)==e['sha256'] and q.stat().st_size==e['bytes']
 verify_sources(context,si)
def budget(state,before_launch=True):
 return aggregate_budget(context,state,receipts,before_launch)['seconds']

def interrupted(signum,frame):raise InterruptedError('controller termination '+str(signum))
for sig in CATCHABLE:signal.signal(sig,interrupted)
try:
 record('controller-start01.json',report)
 for ordinal,module in enumerate(remaining,59):
  proc=None;tracker=None
  assert time.monotonic()-started<3540,'controller wall bound'
  ready=D/'admissions'/f'ready-{ordinal:04d}.json';waiting=time.monotonic();heartbeat=0
  incomplete_ready_since=None
  while True:
   assert time.monotonic()-waiting<600 and time.monotonic()-started<3540,'bounded exact admission wait expired'
   metadata_size()
   if ready.exists():
    try:bounded_json(ready,16384)
    except json.JSONDecodeError:
     # O_EXCL publication is briefly visible before its fsynced payload. Treat
     # only incomplete JSON as not-yet-published for at most TWO seconds.
     if incomplete_ready_since is None:incomplete_ready_since=time.monotonic()
     assert time.monotonic()-incomplete_ready_since<2,'incomplete published readiness refused'
    else:break
   if time.monotonic()-waiting>=heartbeat:
    print(json.dumps({'waiting_exact_ordinal':ordinal,'seconds':time.monotonic()-waiting}),flush=True);heartbeat+=15
   time.sleep(.5)
  identities();assert current_state(ledger,receipts,si['ledger_genesis_sha256'],context)==previous
  ad,external,binding=exact_dispatch(D,ordinal,module,a.config_sha256,source_pin,runner_pin,previous)
  assert ad['continuation_context_sha256']==si['continuation_context_sha256']
  assert ad['limits']==cfg['limits'] and ad['runner_sha256']==sha(Q/'maintained/build_successor_bounded.py') and ad['source_sha256']==si['modules'][module]['sha256']
  assert ad['prior_charged_seconds']==budget(previous)
  ap=D/'admissions'/f'admission-{ordinal:04d}.json';before_raw=(ledger/'ledger.jsonl').read_bytes()
  command=[sys.executable,'-I','-B','-S',str(Q/'maintained/build_successor_bounded.py')]
  for n,v in [('inventory',Q/'maintained-inventory06.json'),('inventory-sha256',runner_pin),('source-inventory',Q/'source-inventory06.json'),('source-inventory-sha256',source_pin),('imports',R/'work/mac-poseidon-call1-plan14/successor-source02/probe-imports01.json'),('workspace',workspace),('output-dir',receipts),('root',R),('admission',ap),('admission-sha256',binding['admission_sha256']),('module',module)]:command.extend(['--'+n,str(v)])
  stdout=O/f'runner-{ordinal:04d}.stdout.txt';stderr=O/f'runner-{ordinal:04d}.stderr.txt'
  record(f'invocation-{ordinal:04d}.json',{'module':module,'ordinal':ordinal,'command':command,'parent_bindings':binding,'prior_state':previous})
  guard.block()
  try:
   with stdout.open('x') as out,stderr.open('x') as err:
    # G1 recheck EVERY still-unbuilt name immediately before invocation.
    assert object_freshness(workspace,remaining[ordinal-59:])==61-ordinal
    proc=subprocess.Popen(command,env=dict(os.environ,LEAN_NUM_THREADS='1'),stdout=out,stderr=err,start_new_session=True,preexec_fn=guard.child_unmask)
    tracker=OwnedRunner(proc)
    guard.restore()
    launch=time.monotonic();last=0
    while proc.poll() is None:
     tracker.observe();metadata_size()
     assert time.monotonic()-launch<=300 and time.monotonic()-started<3540,'runner/controller wall bound'
     assert stdout.stat().st_size<=65536 and stderr.stat().st_size<=65536,'bounded controller runner output'
     if time.monotonic()-launch>=last:
      print(json.dumps({'running_exact_module':module,'seconds':time.monotonic()-launch}),flush=True);last+=15
     time.sleep(.25)
  finally:
   if proc is not None:
    if tracker is None:tracker=OwnedRunner(proc)
    cleanup=tracker.cleanup()
    record(f'cleanup-{ordinal:04d}.json',cleanup)
   guard.restore()
  assert cleanup['leader_reaped'] and not cleanup['errors'] and not cleanup['remaining_owned_groups']
  assert proc.returncode==0,'runner failure/refusal/interruption => STOP; no retry/nextmodule'
  rec=receipts/receipt_name(ordinal,module);obj=workspace/'.lake/build/lib/lean/ShielddSecurity'/(module+'.olean');src=source_path(si,module,workspace)
  result=checked_result(rec,rec.with_suffix('.log'),src,obj,binding['admission_sha256'],validate,workspace/'.lake/build/lib/lean/ShielddSecurity')
  assert result['axiom_audits']==cfg['expected_audit_counts'][module]
  identities();current=current_state(ledger,receipts,si['ledger_genesis_sha256'],context);after_raw=(ledger/'ledger.jsonl').read_bytes()
  assert after_raw.startswith(before_raw) and len(after_raw.splitlines())==len(before_raw.splitlines())+3
  assert current['launch_intents']==current['consumed_claims']==ordinal
  assert all(current['receipts'].get(n)==h for n,h in previous['receipts'].items()) and all(current['claims'].get(n)==h for n,h in previous['claims'].items())
  budget(current,before_launch=False)
  record(f'raw-result-{ordinal:04d}.json',{'module':module,'receipt_sha256':sha(rec),'log_sha256':sha(rec.with_suffix('.log')),'audits':result['axiom_audits'],'seconds':result['seconds'],'current_state':current,'classification':'worker observation only; next exact admission still requires PARENT raw acceptance and frozen external anchor'})
  report['actual_modules_invoked'].append({'module':module,'ordinal':ordinal,'receipt_sha256':sha(rec)});previous=current
  # No next name until parent publishes next separately anchored readiness.
 report.update(status='all2-finaltwo-results-observed',final_state=previous,full_transfer='OPEN')
except BaseException as e:
 report.update(status='STOPPED',error_type=type(e).__name__,reason=str(e),no_retry_or_reset=True)
finally:
 old={sig:signal.getsignal(sig) for sig in CATCHABLE}
 try:
  for sig in old:signal.signal(sig,signal.SIG_IGN)
  if proc is not None and proc.poll() is None:
   if tracker is None:tracker=OwnedRunner(proc)
   report['backup_cleanup']=tracker.cleanup()
  guard.restore();report['controller_seconds']=time.monotonic()-started;record('controller-final01.json',report)
 finally:
  fcntl.flock(lockfd,fcntl.LOCK_UN);os.close(lockfd)
  for sig,handler in old.items():signal.signal(sig,handler)
print(json.dumps(report),flush=True);sys.exit(0 if report['status']=='all2-finaltwo-results-observed' else 1)
