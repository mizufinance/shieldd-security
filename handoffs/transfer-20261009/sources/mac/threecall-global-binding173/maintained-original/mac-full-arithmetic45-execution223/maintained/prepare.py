from pathlib import Path
import json,hashlib,re,os,ast,difflib
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');W=R/'work';P=W/'mac-full-arithmetic45-execution220';S=W/'mac-full-arithmetic45-execution223'
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
# Exact old phase bytes remain immutable and every cost/failure is carried.
c=json.loads((P/'config01.json').read_bytes());history=json.loads(Path(c['carried_failure']['path']).read_bytes());raw=(P/'runtime/ledger.jsonl').read_bytes();events=[json.loads(x)for x in raw.splitlines()]
require(raw.endswith(b'\n')and len(events)%2==0 and events[-1]['kind']=='result','completed phase ledger')
rps=[x['receipt']for x in events if x['kind']=='result'];current=[json.loads(Path(p['path']).read_bytes())for p in rps]
require(all(r['status']=='passed'and type(r['exit'])is int and r['exit']==0 and r['cleanup']['clean']and r['cleanup']['leader_reaped']for r in current),'all current accepted; no new failure exception')
require(current[-1]['module']=='CapturedThreeCallGlobalBinding173J103','exact completed boundary after zero-intent lock-contention refusal')
receipts=history['receipts']+rps;rs=[json.loads(Path(p['path']).read_bytes())for p in receipts]
require(len(rs)==1185 and sum(r['status']=='failed'for r in rs)==124,'exact historical1185/124 state')
require(all(r['cleanup']['clean'] for r in rs),'historical cleanup')
require(not S.exists(),'new immutable phase');S.mkdir();entries={};links={}
for p in P.rglob('*'):
 if p.is_symlink():v=pin(p.resolve());entries[str(p)]=dict(path=str(p),symlink_target=os.readlink(p),target=v);links[str(p)]=v
 elif p.is_file():entries[str(p)]=pin(p)
put('protected-history01.json',dict(parents=[c['carried_failure']],roots=[str(P)],entries=entries,historical_aliases=links,receipts=receipts,expected_statuses=[r['status']for r in rs],consumed_attempts=len(rs),consumed_lean_seconds=sum(r['lean_seconds']for r in rs)))
for rp,r in zip(rps,current):
 n=r['module'];cache=Path(r['command'][r['command'].index('-o')+1]).parent
 c['qualified_batch_imports'][n]=dict(source=r['source'],object=r['objects'][str(cache/(n+'.olean'))],receipt=rp,current_slots={suffix:r['objects'].get(str(cache/(n+suffix)))for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']},custom_imports=re.findall(r'^import (ShielddSecurity\.[\w.]+)\s*$',Path(r['source']['path']).read_text(),re.M),fresh_execution_credit=0,legacy_signature_inventory_absent=False)
# Strictly apply SOURCE222's maintained delta by in-memory source construction.
old=(P/'maintained/guard.py').read_text();require(pin(P/'maintained/guard.py')['sha256']=='cc900fcc6e04d03ceab5c14d686323fcce1cf9e45d597a4f591ee257cbf50bc0','exact old executor')
helper=(W/'mac-resource-preflight222-source01/physical-preflight.py').read_text();new=old.replace('def bounds(config):',helper+'def bounds(config):',1);new=new.replace('cancelled();pre=bounds(config);launch_reserve(pre)','cancelled();physical_preflight(config)',2);new=new.replace('if not cache.exists(): initialize_overlay(config)','if not cache.exists():\n            pre=bounds(config);launch_reserve(pre);initialize_overlay(config)',1)
new=new.replace("actual.update(key for key in preserved_configs() if any(pathlib.Path(key).is_relative_to(pathlib.Path(root)) for root in roots))","require(all(root.startswith('/') and '..' not in root.split('/') and '//' not in root and not root.endswith('/') for root in roots), 'canonical historical directory roots')\n        actual.update(key for key in preserved_configs() if any(key.startswith(root+'/') for root in roots))",1)
report=json.loads((W/'mac-resource-preflight222-source01/data-report01.json').read_bytes());require(len(new.encode())==report['derived_guard_bytes']and hashlib.sha256(new.encode()).hexdigest()==report['derived_guard_sha256'],'exact reviewed SOURCE delta derivation');ast.parse(new)
(S/'maintained').mkdir();(S/'maintained/guard.py').write_text(new);(S/'maintained/prepare.py').write_bytes(Path(__file__).read_bytes());put('maintained-inventory01.json',{p.name:pin(p)for p in (S/'maintained').iterdir()})
root=W/'mac-boolean-root209-source02';generation=json.loads((root/'generation01.json').read_bytes());g=generation['outputs'][0];require(g['name']=='CapturedBooleanRoot209'and pin(g['source']['path'])==g['source'],'maintained root revision')
c['modules'][g['name']]=dict(source=g['source'],source_root=str(root/'source-root'),audits=g['audits'],imports=re.findall(r'^import ([\w.]+)\s*$',Path(g['source']['path']).read_text(),re.M))
for root in [W/'mac-resource-preflight222-source01',W/'mac-accounting-cache221-source02',W/'mac-boolean-root209-source02']:
 c['charged_roots'].append(str(root))
 for p in root.rglob('*'):
  if p.is_file()and not p.is_symlink():c['static_records'][str(p)]=pin(p)
order=[n for n in c['order']if n not in c['qualified_batch_imports']];require(len(order)==544 and order[0]=='CapturedThreeCallGlobalBinding173J104','exact remaining order')
c.update(batch_root=str(S),maintained=str(S/'maintained'),own_cache=str(S/'own-cache'),runtime=str(S/'runtime'),carried_attempts=len(rs),carried_lean_seconds=sum(r['lean_seconds']for r in rs),carried_failure=pin(S/'protected-history01.json'),order=order)
c['charged_roots'].append(str(S));c['charged_roots']=list(dict.fromkeys(c['charged_roots']));c['lean_path'][0]=c['own_cache'];c['lean_environment']['LEAN_PATH']=':'.join(c['lean_path'])
(S/'dispatcher').mkdir();(S/'dispatcher/serial.py').write_bytes((P/'dispatcher/serial.py').read_bytes())
for p in [Path(__file__),S/'dispatcher/serial.py',*list((S/'maintained').iterdir())]:c['static_records'][str(p)]=pin(p)
closure=json.loads(Path(c['closure']['path']).read_bytes())['modules'];closure.update(c['qualified_batch_imports']);aliases={}
for n,d in closure.items():
 for suffix,v in d['current_slots'].items():
  if v is not None:aliases[str(S/'own-cache/ShielddSecurity'/(n+suffix))]=v
put('overlay-manifest01.json',dict(aliases=aliases,closure=c['closure']));c['overlay_manifest']=pin(S/'overlay-manifest01.json');put('config01.json',c)
put('plan01.json',dict(config=pin(S/'config01.json'),inventory=pin(S/'maintained-inventory01.json'),inherited=c['carried_failure'],remaining_named=len(order),no_accepted_replay=True,guard_delta=pin(W/'mac-resource-preflight222-source01/producer-manifest01.json'),unchanged_machine_limits=True,source_revision='20902 omits unused CharP hypothesis on unselected_input, pins actual accepted20705; all conclusions unchanged',scope='Join binding through J103 qualified, final J104/root still UNRUN; actual Boolean-slot/kernel coverage follows global Join binding. No full legal-Transfer/native conclusion. No cumulative quotas.'))
put('transition-observation01.json',dict(scope='ZERO_INTENT_PRELAUNCH_REFUSAL',old_phase=str(P),last_pass=current[-1]['module'],ledger=pin(P/'runtime/ledger.jsonl'),cause='Owned boundary DATA monitor briefly held nonblocking Gate; dispatcher refused before J104 claim. No compiler failure or duplicated verifier. Monitor stopped; new phase carries all1185 receipts and unused J104 admission.',failure_credit=0,source=pin(Path('/tmp/stop_execution220_after_join.py'))))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),preserved_inputs=c['carried_failure']));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),carried_attempts=len(rs),failed=124,first=order[:3],remaining=len(order),guard=pin(S/'maintained/guard.py'),producer=pin(S/'producer-manifest01.json'))))
