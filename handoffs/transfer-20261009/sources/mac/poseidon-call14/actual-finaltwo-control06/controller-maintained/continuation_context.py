"""Pure continuation bindings. Local state requires an external parent rollback anchor."""
import hashlib,json,math
from pathlib import Path
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
FUTURE=['TransferPoseidonCall14Proof01','TransferPoseidonCall14CheckedControls01']
def module_at(ordinal,original):
 assert type(ordinal) is int and 1<=ordinal<=60,'ordinal61 unmapped; no spare job'
 if ordinal<=55:return original[ordinal-1]
 return 'TransferPoseidonCall14Program01' if ordinal in [56,57] else 'TransferPoseidonCall14Proof01' if ordinal==58 else FUTURE[ordinal-59]
def receipt_name(ordinal,module):
 assert type(ordinal) is int and 1<=ordinal<=60
 return 'build-'+module+('-03.json' if ordinal==57 else '-02.json' if ordinal in [56,59] else '-01.json')
def load_context(path,pin):
 assert path.is_file() and not path.is_symlink() and sha(path)==pin
 c=json.loads(path.read_bytes());assert c['schema']=='Call14-fixed-failed55-56-58-finaltwo06'
 assert c['initial_state']['launch_intents']==58 and c['initial_state']['ledger_events']==174
 assert sha(Path(c['parent_anchor']['path']))==c['parent_anchor']['sha256']
 assert json.loads(Path(c['parent_anchor']['path']).read_bytes())['state']==c['initial_state']
 return c
def check_record(path,entry):
 assert path.is_file() and not path.is_symlink() and sha(path)==entry['sha256'] and path.stat().st_size==entry['bytes'],'frozen identity changed: '+str(path)
def verify_fixed(c):
 for p,e in c['fixed_records'].items():check_record(Path(p),e)
def verify_sources(c,si):
 verify_fixed(c)
 objects=Path(c['protected_object_cache'])
 for name,entry in c['protected_custom_objects'].items():
  obj=objects/(name+'.olean');assert (sha(obj) if obj.exists() else None)==entry['object_sha256'],'qualified/custom object changed'
  actual={part.name:sha(part) for suffix in ['.olean.private','.olean.server','.ilean','.ir'] if (part:=obj.with_suffix(suffix)).exists()}
  assert actual==entry['parts'],'exact old custom companion identity set changed'
 assert si['lean_source_root']==c['module_source_root'],'explicit command root must match canonical source root'
 root=Path(c['module_source_root'])
 assert {p.name for p in root.iterdir()}=={'ShielddSecurity','emission06.json'}
 assert {p.name for p in (root/'ShielddSecurity').iterdir()}=={n+'.lean' for n in FUTURE}
 for n in FUTURE:verify_module_source(c,si,n)
 for n,e in si['modules'].items():check_record(Path(e['path']),e)
 # Original source files including the failed Program remain immutable.
 for p,e in c['original_source_records'].items():check_record(Path(p),e)
def verify_module_source(c,si,name):
 root=Path(c['module_source_root']);p=Path(si['modules'][name]['path'])
 assert root.is_dir() and not root.is_symlink() and root.resolve()==root
 assert p.is_file() and not p.is_symlink() and p.resolve()==p
 assert p.parent.name=='ShielddSecurity' and p.parent.parent==root
 canonical='.'.join(p.relative_to(root).with_suffix('').parts)
 assert canonical=='ShielddSecurity.'+name,'canonical source-root module mismatch'
 check_record(p,si['modules'][name]);return canonical
def source_path(si,name,workspace):
 return Path(si['modules'][name]['path']) if name in si['modules'] else workspace/'ShielddSecurity'/(name+'.lean')
def validate_history(c,state,events,receipts,ledger,original):
 initial=c['initial_state'];assert 58<=state['launch_intents']<=60
 assert state['ledger_events']==3*state['launch_intents'] and len(events)==state['ledger_events']
 raw=(ledger/'ledger.jsonl').read_bytes();lines=raw.splitlines(keepends=True)
 assert hashlib.sha256(b''.join(lines[:174])).hexdigest()==initial['ledger_sha256'],'fixed failed55+56+58 prefix changed'
 for key in ['receipts','claims']:
  assert all(state[key].get(n)==h for n,h in initial[key].items()),'fixed history changed/deleted'
 assert state['genesis_sha256']==initial['genesis_sha256']
 for index in range(state['launch_intents']):
  ordinal=index+1;triplet=events[3*index:3*index+3];module=module_at(ordinal,original)
  assert [e['kind'] for e in triplet]==['claim_consumed','launch_intent','final']
  assert all(type(e['ordinal']) is int and e['ordinal']==ordinal and e['module']==module for e in triplet)
  assert all(e['claim']==triplet[0]['claim'] for e in triplet)
  slot=receipt_name(ordinal,module);assert triplet[1]['receipt_name']==triplet[2]['receipt_name']==slot
  row=json.loads((receipts/slot).read_bytes())
  if slot in c['failed_receipts']:
   assert ordinal in [55,56,58] and state['receipts'][slot]==c['failed_receipts'][slot] and row['status']=='failed','only exact failed55+56+58 exceptions'
  else:
   assert row['status']=='passed' and type(row['exit']) is int and row['exit']==0,'ANY new nonpassed launch stops continuation'
  assert row['module']==module
 return state
def receipt_available(receipts,ordinal,module):
 slot=receipt_name(ordinal,module)
 assert not (receipts/slot).exists() and not (receipts/slot).with_suffix('.log').exists(),'target receipt/log slot stale'
 existing={p.name for p in receipts.glob('build-'+module+'-*.json')}|{p.name for p in receipts.glob('build-'+module+'-*.log')}
 permitted={'build-'+module+'-01.'+suffix for suffix in ['json','log']} if ordinal==59 else set()
 assert existing==permitted,'unaccounted same-target slot; no retry/reset'
 return slot
def charged_files(c):
 # Every physical Call14 source/object copy in its work/output roots is charged.
 # These roots include both parent regeneration copies, all readiness stages,
 # all repairs and fixtures. Code/templates are also conservatively charged.
 assert c['additional_own_physical_names']==[FUTURE[1]],'Combined additional physical own name required'
 names=set(c['original_names'])|set(c['additional_own_physical_names']);found={}
 for directory in c['charged_roots']:
  root=Path(directory);assert root.is_dir() and not root.is_symlink()
  for p in root.rglob('*'):
   if p.is_symlink():
    assert str(p) in c['historical_symlinks'] and str(p.readlink())==c['historical_symlinks'][str(p)]['target'],'new/changed symlink in charged root'
    if p.is_dir():continue
    assert sha(p)==c['historical_symlinks'][str(p)]['target_sha256']
    # Retained deliberate symlink-control fixture counted conservatively.

   if not p.is_file():continue
   own=any(p.name==n+'.lean' or p.name.startswith(n+'.olean') or p.name==n+'.ilean' or p.name==n+'.ir' for n in names)
   code=p.suffix=='.py' or p.name.endswith('.lean.txt')
   if own or code:found[str(p)]=p.stat().st_size
   assert len(found)<=20000,'bounded charged physical file census'
 return found
def runtime_metadata_size(c):
 total=0
 for directory in c['runtime_metadata_roots']:
  d=Path(directory)
  if not d.exists():continue
  assert d.is_dir() and not d.is_symlink()
  for p in d.iterdir():
   assert p.is_file() and not p.is_symlink(),'flat runtime metadata required'
   total+=p.stat().st_size
 assert total<=16*1024**2,'combined retained-old+new runtime metadata16MiB bound'
 return total
def charged_total(c):
 files=charged_files(c);reserves={directory:max(0,floor-sum(value for path,value in files.items() if path.startswith(directory+'/'))) for directory,floor in c['conservative_copy_floors'].items()}
 return sum(files.values())+sum(reserves.values()),files,reserves
def aggregate_budget(c,state,receipts,before_launch=False):
 rows=[json.loads((receipts/n).read_bytes()) for n in state['receipts']]
 for r in rows:
  value=r.get('seconds',0);assert type(value) in [int,float] and math.isfinite(value) and value>=0,'nonfinite attempt accounting'
 total=sum(r.get('seconds',0) for r in rows if r.get('command_started'))
 assert type(state['launch_intents']) is int and state['launch_intents']<=60
 assert total<=1200 and (not before_launch or total<1200)
 amount,files,reserves=charged_total(c);assert amount<=512*1024**2,'ALL physical source/object copies exceed512MiB'
 return {'attempts':state['launch_intents'],'seconds':total,'charged_source_object_bytes':amount,'physical_source_object_bytes':sum(files.values()),'copy_floor_reserves':reserves,'physical_files':len(files)}
