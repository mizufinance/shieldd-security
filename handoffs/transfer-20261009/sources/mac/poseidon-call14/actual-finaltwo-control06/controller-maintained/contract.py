"""Exact parent dispatch bindings and RAW result checks; never issues admissions."""
import hashlib,json,math,re
from pathlib import Path
from continuation_context import validate_history
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def bounded_json(path,maximum):
 assert path.is_file() and not path.is_symlink(),'missing/symlink parent dispatch file'
 assert path.stat().st_size<=maximum,'bounded dispatch JSON exceeded'
 return json.loads(path.read_text())
def closed(directory,inventory,executing):
 assert {p.name for p in directory.iterdir()}==set(inventory['maintained_files'])
 for n,e in inventory['maintained_files'].items():
  p=directory/n;assert p.is_file() and not p.is_symlink() and sha(p)==e['sha256'] and p.stat().st_size==e['bytes']
 assert sha(executing)==inventory['maintained_files'][executing.name]['sha256']
def exact_dispatch(dispatch,ordinal,module,config_sha256,source_sha256,maintained_sha256,previous_state):
 feed=dispatch/'admissions';ready=feed/f'ready-{ordinal:04d}.json'
 meta=bounded_json(ready,16384)
 assert set(meta)=={'module','ordinal','admission_sha256','config_sha256'}
 assert meta['ordinal']==ordinal and meta['module']==module and meta['config_sha256']==config_sha256
 admission=feed/f'admission-{ordinal:04d}.json';anchor=dispatch/'observations'/f'anchor-{ordinal-1:04d}.json'
 a=bounded_json(admission,32768);external=bounded_json(anchor,131072)
 assert sha(admission)==meta['admission_sha256'] and sha(anchor)==a['parent_latest_anchor_sha256']
 assert a['kernel_admission'] is True and a['successor_kernel_admission'] is True
 assert a['module']==module and a['expected_ordinal']==ordinal and a['dispatch_config_sha256']==config_sha256
 assert a['source_inventory_sha256']==source_sha256 and a['maintained_inventory_sha256']==maintained_sha256
 assert a['expected_prior_state']==external['state']==previous_state
 assert ordinal-1==previous_state['launch_intents']==previous_state['consumed_claims']
 assert len(previous_state['receipts'])==ordinal-1 and previous_state['ledger_events']==3*(ordinal-1)
 assert math.isfinite(a['prior_charged_seconds']) and 0<=a['prior_charged_seconds']<1200
 return a,external,{'readiness_sha256':sha(ready),'admission_sha256':sha(admission),'anchor_sha256':sha(anchor)}
def current_state(ledger,receipts,genesis_sha256,context):
 """Reuse exact live accounting without importing/spawning runner or taking its lock."""
 assert ledger.is_dir() and not ledger.is_symlink() and receipts.is_dir() and not receipts.is_symlink()
 for p in [ledger/'ledger.jsonl',ledger/'genesis01.json',*(ledger/'claims').iterdir(),*receipts.glob('build-*.json')]:assert p.is_file() and not p.is_symlink()
 raw=(ledger/'ledger.jsonl').read_bytes();assert raw.endswith(b'\n');events=[];claims={};intents={};final={};previous='0'*64
 for line in raw.splitlines(keepends=True):
  e=json.loads(line);assert (json.dumps(e,sort_keys=True,separators=(',',':'))+'\n').encode()==line
  assert e['sequence']==len(events)+1 and e['previous_event_sha256']==previous
  previous=hashlib.sha256(line).hexdigest();events.append(e)
  if e['kind']=='claim_consumed':assert e['claim']['name'] not in claims;claims[e['claim']['name']]=e['claim']['sha256']
  elif e['kind']=='launch_intent':assert e['receipt_name'] not in intents;intents[e['receipt_name']]=e
  elif e['kind']=='final':assert e['receipt_name'] not in final and e['receipt_name'] in intents;final[e['receipt_name']]=e['receipt_sha256']
  else:raise AssertionError('unknown ledger kind')
 assert len(events)==3*len(intents)==3*len(claims)==3*len(final),'incomplete/consumed transition; stop'
 assert {p.name:sha(p) for p in (ledger/'claims').iterdir()}==claims
 assert {p.name:sha(p) for p in receipts.glob('build-*.json')}==final and set(final)==set(intents)
 assert sha(ledger/'genesis01.json')==genesis_sha256
 state={'ledger_sha256':hashlib.sha256(raw).hexdigest(),'ledger_events':len(events),'launch_intents':len(intents),'consumed_claims':len(claims),'receipts':final,'claims':claims,'genesis_sha256':genesis_sha256}
 validate_history(context,state,events,receipts,ledger,context['original_names'])
 return state
def object_freshness(workspace,names):
 objects=workspace/'.lake/build/lib/lean/ShielddSecurity'
 assert objects.is_dir()
 found={n:[str(p) for p in objects.glob(n+'.*')] for n in names}
 assert not any(found.values()),'G1: still-unbuilt target object/companion exists'
 return len(names)
def checked_result(receipt,log,source,obj,admission_sha256,validate,objects):
 d=bounded_json(receipt,2*1024**2)
 assert d['status']=='passed' and type(d['exit']) is int and d['exit']==0 and d['command_started'] is True
 assert d['admission_sha256']==admission_sha256 and d['source_sha256']==sha(source) and d['object_sha256']==sha(obj)
 assert d['source_bytes']==source.stat().st_size and d['object_bytes']==obj.stat().st_size
 assert d['log_sha256']==sha(log) and log.stat().st_size<=16*1024**2
 actual=validate(log.read_text(),d['expected_axiom_names'],d['expected_signature_names'])
 assert actual['full_signature_sha256']==d['full_signature_sha256'] and actual['axiom_audits']==d['axiom_audits']
 assert all(type(d[k]) in [int,float] and math.isfinite(d[k]) and 0<=d[k]<=v for k,v in [('seconds',240),('peak_group_rss_bytes',4294967296)])
 assert d['minimum_memory_free_percent']>=15 and d['minimum_disk_free_bytes']>=2147483648
 assert d['owned_cleanup']['leader_reaped'] and not d['owned_cleanup']['errors']
 for name,entry in d['frozen_imports'].items():
  if name in ['package','official_import_closure']:continue
  imported=objects/(name+'.olean')
  assert entry['parts']=={part.name:sha(part) for suffix in ['.olean.private','.olean.server','.ilean','.ir'] if (part:=imported.with_suffix(suffix)).exists()},'exact custom companions including ir'
 return d
