from pathlib import Path
import json,hashlib,re,os,ast
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');W=R/'work';P=W/'mac-full-arithmetic45-execution223';S=W/'mac-full-arithmetic45-execution224'
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
c=json.loads((P/'config01.json').read_bytes());history=json.loads(Path(c['carried_failure']['path']).read_bytes());raw=(P/'runtime/ledger.jsonl').read_bytes();events=[json.loads(x)for x in raw.splitlines()]
require(raw.endswith(b'\n')and len(events)==52 and events[-1]['kind']=='result','exact clean26-job checkpoint')
rps=[x['receipt']for x in events if x['kind']=='result'];current=[json.loads(Path(p['path']).read_bytes())for p in rps]
require(all(r['status']=='passed'and type(r['exit'])is int and r['exit']==0 and r['cleanup']['clean']and r['cleanup']['leader_reaped']for r in current),'all current accepted')
require(current[-1]['module']=='CapturedBooleanSlots208B0034','exact checkpoint boundary')
receipts=history['receipts']+rps;rs=[json.loads(Path(p['path']).read_bytes())for p in receipts]
require(len(rs)==1211 and sum(r['status']=='failed'for r in rs)==124,'complete immutable consumed history')
require(all(r['cleanup']['clean']for r in rs),'previous cleanup')
require(not S.exists(),'fresh immutable executor namespace');S.mkdir();entries={};links={}
for p in P.rglob('*'):
 if p.is_symlink():v=pin(p.resolve());entries[str(p)]=dict(path=str(p),symlink_target=os.readlink(p),target=v);links[str(p)]=v
 elif p.is_file():entries[str(p)]=pin(p)
put('protected-history01.json',dict(parents=[c['carried_failure']],roots=[str(P)],entries=entries,historical_aliases=links,receipts=receipts,expected_statuses=[r['status']for r in rs],consumed_attempts=len(rs),consumed_lean_seconds=sum(r['lean_seconds']for r in rs)))
for rp,r in zip(rps,current):
 n=r['module'];cache=Path(r['command'][r['command'].index('-o')+1]).parent
 c['qualified_batch_imports'][n]=dict(source=r['source'],object=r['objects'][str(cache/(n+'.olean'))],receipt=rp,current_slots={suffix:r['objects'].get(str(cache/(n+suffix)))for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']},custom_imports=re.findall(r'^import (ShielddSecurity\.[\w.]+)\s*$',Path(r['source']['path']).read_text(),re.M),fresh_execution_credit=0,legacy_signature_inventory_absent=False)
old=(P/'maintained/guard.py').read_bytes();require(hashlib.sha256(old).hexdigest()=='8d158b110e0941a502750e1188ad6580ee7672eecdd2147a049ad077c5a97c2a','unchanged qualified physical/identity guard');ast.parse(old)
(S/'maintained').mkdir();(S/'maintained/guard.py').write_bytes(old);(S/'maintained/prepare.py').write_bytes(Path(__file__).read_bytes());put('maintained-inventory01.json',{p.name:pin(p)for p in (S/'maintained').iterdir()})
roots=[W/'mac-word-hints210-source01',W/'mac-word-hints210-source02',W/'mac-word-hints210-source03',W/'mac-word-slots211-source01',W/'mac-word-shared212-source01',W/'mac-word-shared212-source02',W/'mac-word-root213-source01',W/'mac-original-tag214-source01',W/'mac-original-tag214-source02']
fresh={}
for root in [roots[2],roots[3],roots[5],roots[6],roots[8]]:
 g=json.loads((root/'generation01.json').read_bytes())
 for o in g['outputs']:
  require(pin(o['source']['path'])==o['source'],'exact immutable maintained generated source')
  n=o['name'];require(n not in c['modules']and n not in c['qualified_batch_imports'],'fresh namespace no replay')
  c['modules'][n]=dict(source=o['source'],source_root=str(root/'source-root'),audits=o['audits'],imports=re.findall(r'^import ([\w.]+)\s*$',Path(o['source']['path']).read_text(),re.M));fresh[n]=str(root)
for root in roots:
 c['charged_roots'].append(str(root))
 for p in root.rglob('*'):
  if p.is_file()and not p.is_symlink():c['static_records'][str(p)]=pin(p)
remaining=[n for n in c['order']if n not in c['qualified_batch_imports']]
boolean=[n for n in remaining if n.startswith('CapturedBooleanSlots208')or n=='CapturedBooleanRoot209']
other=[n for n in remaining if n not in boolean]
order=['WordHints210','SharedWordSeed212','CapturedOriginalTag214']+boolean+sorted(n for n in fresh if n.startswith('CapturedWordSlots211'))+['CapturedWordRoot213']+other
require(len(order)==len(set(order))and len(order)==len(remaining)+21,'complete exact remaining topology plus21fresh names')
available=set(c['qualified_batch_imports'])|set(json.loads(Path(c['closure']['path']).read_bytes())['modules'])
for n in order:
 for imported in c['modules'][n]['imports']:
  if imported.startswith('ShielddSecurity.'):require(imported.split('.',1)[1]in available,'exact custom dependency before '+n)
 available.add(n)
c.update(batch_root=str(S),maintained=str(S/'maintained'),own_cache=str(S/'own-cache'),runtime=str(S/'runtime'),carried_attempts=len(rs),carried_lean_seconds=sum(r['lean_seconds']for r in rs),carried_failure=pin(S/'protected-history01.json'),order=order)
c['charged_roots'].append(str(S));c['charged_roots']=list(dict.fromkeys(c['charged_roots']));c['lean_path'][0]=c['own_cache'];c['lean_environment']['LEAN_PATH']=':'.join(c['lean_path'])
(S/'dispatcher').mkdir();(S/'dispatcher/serial.py').write_bytes((P/'dispatcher/serial.py').read_bytes())
for p in [Path(__file__),S/'dispatcher/serial.py',*list((S/'maintained').iterdir())]:c['static_records'][str(p)]=pin(p)
closure=json.loads(Path(c['closure']['path']).read_bytes())['modules'];closure.update(c['qualified_batch_imports']);aliases={}
for n,d in closure.items():
 for suffix,v in d['current_slots'].items():
  if v is not None:aliases[str(S/'own-cache/ShielddSecurity'/(n+suffix))]=v
put('overlay-manifest01.json',dict(aliases=aliases,closure=c['closure']));c['overlay_manifest']=pin(S/'overlay-manifest01.json');put('config01.json',c)
put('transition-observation01.json',dict(scope='SAFE_OWNED_DISPATCHER_CHECKPOINT_ZERO_NEW_INTENT',old_phase=str(P),ledger=pin(P/'runtime/ledger.jsonl'),last_pass=current[-1]['module'],stop_source=pin(Path('/tmp/stop_execution223_at_boundary.py')),effect='SIGTERM cancellation flag with held lock and no verifier, before next claim; no failure/duplicate successful compile. Unused next admission is preserved.'))
put('plan01.json',dict(config=pin(S/'config01.json'),inventory=pin(S/'maintained-inventory01.json'),inherited=c['carried_failure'],remaining_named=len(order),new_names=list(fresh),guard_unchanged=pin(S/'maintained/guard.py'),no_accepted_replay=True,scope='Autonomous word/tag first-leaf qualification, then remaining original Boolean seed/root and66 actual word instances/root, then full hash/path coverage. Common encoding compatibility and semantic roles explicit; all fresh sources UNRUN. No cumulative quota, fixed per-run machine safeguards unchanged.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),preserved_inputs=c['carried_failure']));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),carried_attempts=len(rs),failures=124,first=order[:4],remaining=len(order),guard=pin(S/'maintained/guard.py'),producer=pin(S/'producer-manifest01.json'))))
