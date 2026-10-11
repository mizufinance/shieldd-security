"""Pinned finite serial delegation; every job uses the complete current-byte guard."""
from pathlib import Path
import argparse,hashlib,json,runpy,signal,sys,types
S=Path(__file__).resolve().parent.parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def main():
 require(sys.flags.isolated==1 and sys.flags.dont_write_bytecode==1 and sys.flags.no_site==1 and sys.flags.optimize==0,'isolated Python')
 parser=argparse.ArgumentParser();parser.add_argument('--max-jobs',type=int,required=True);args=parser.parse_args();require(1<=args.max_jobs<=32,'finite serial chunk')
 config=S/'config01.json';inventory=S/'maintained-inventory01.json';c=json.loads(config.read_bytes());mi=json.loads(inventory.read_bytes())
 require(c['static_records'][str(Path(__file__))]==pin(Path(__file__)),'exact executing dispatcher')
 guard=S/'maintained/guard.py';require(mi['guard.py']==pin(guard),'exact guarded executor')
 g=runpy.run_path(str(guard),run_name='pinned_serial_guard')
 for sig in g['TERMS']:signal.signal(sig,g['cancellation'])
 for _ in range(args.max_jobs):
  g['cancelled']();require(c['static_records'][str(Path(__file__))]==pin(Path(__file__)) and mi['guard.py']==pin(guard),'unchanged executable sources')
  current=json.loads(config.read_bytes());current['_config_sha256']=pin(config)['sha256'];current['_inventory_sha256']=pin(inventory)['sha256']
  records,digest=g['state'](current)
  if len(records)==len(current['order']):break
  name=current['order'][len(records)];a=dict(approved=True,authorization='Human/parent autonomous implementing delegate; finite serial jobs, unchanged host safety; no old admission fabricated.',config_sha256=pin(config)['sha256'],inventory_sha256=pin(inventory)['sha256'],module=name,prior_ledger_sha256=digest,prior_passed=len(records),carried_failure_sha256=current['carried_failure']['sha256'])
  admission=S/('delegate-'+name+'-admission01.json');g['create'](admission,a)
  job=types.SimpleNamespace(config=str(config),config_sha256=a['config_sha256'],inventory=str(inventory),inventory_sha256=a['inventory_sha256'],admission=str(admission),admission_sha256=pin(admission)['sha256'],module=name)
  g['execute'](job)
  print(json.dumps({'serial_module_completed':name}),flush=True)
if __name__=='__main__':main()
