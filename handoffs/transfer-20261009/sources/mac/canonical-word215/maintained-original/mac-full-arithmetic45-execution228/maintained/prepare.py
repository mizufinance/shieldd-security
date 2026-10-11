from pathlib import Path
import json,hashlib,re,os,ast
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');W=R/'work';P=W/'mac-full-arithmetic45-execution226';S=W/'mac-full-arithmetic45-execution228'
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
c=json.loads((P/'config01.json').read_bytes());history=json.loads(Path(c['carried_failure']['path']).read_bytes());raw=(P/'runtime/ledger.jsonl').read_bytes();events=[json.loads(x)for x in raw.splitlines()]
require(raw.endswith(b'\n')and len(events)==2 and events[-1]['kind']=='result','exact failed canonical helper checkpoint')
rps=[x['receipt']for x in events if x['kind']=='result'];current=[json.loads(Path(p['path']).read_bytes())for p in rps]
require(all(r['cleanup']['clean']and r['cleanup']['leader_reaped']for r in current),'all owned cleanup/pass')
receipts=history['receipts']+rps;rs=[json.loads(Path(p['path']).read_bytes())for p in receipts]
require(len(rs)==1225 and sum(r['status']=='failed'for r in rs)==126,'complete consumed history')
require(not S.exists(),'fresh immutable executor');S.mkdir();entries={};links={}
for p in P.rglob('*'):
 if p.is_symlink():v=pin(p.resolve());entries[str(p)]=dict(path=str(p),symlink_target=os.readlink(p),target=v);links[str(p)]=v
 elif p.is_file():entries[str(p)]=pin(p)
put('protected-history01.json',dict(parents=[c['carried_failure']],roots=[str(P)],entries=entries,historical_aliases=links,receipts=receipts,expected_statuses=[r['status']for r in rs],consumed_attempts=len(rs),consumed_lean_seconds=sum(r['lean_seconds']for r in rs)))
for rp,r in zip(rps,current):
 if r['status']!='passed':continue
 n=r['module'];cache=Path(r['command'][r['command'].index('-o')+1]).parent
 c['qualified_batch_imports'][n]=dict(source=r['source'],object=r['objects'][str(cache/(n+'.olean'))],receipt=rp,current_slots={suffix:r['objects'].get(str(cache/(n+suffix)))for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']},custom_imports=re.findall(r'^import (ShielddSecurity\.[\w.]+)\s*$',Path(r['source']['path']).read_text(),re.M),fresh_execution_credit=0,legacy_signature_inventory_absent=False)
old=(P/'maintained/guard.py').read_bytes();require(hashlib.sha256(old).hexdigest()=='8d158b110e0941a502750e1188ad6580ee7672eecdd2147a049ad077c5a97c2a','unchanged physical/identity guard');a=old.index(b'_STORAGE_PIN = ');b=old.index(b'\n_STORAGE =',a);storage=W/'mac-history-metadata-preservation126-29';old=old[:a]+b'_STORAGE_PIN = '+repr(pin(storage/'archive-map01.json')).encode()+old[b:];ast.parse(old)
for p in storage.rglob('*'):
 if p.is_file():c['static_records'][str(p)]=pin(p)
c['charged_roots'].append(str(storage))
(S/'maintained').mkdir();(S/'maintained/guard.py').write_bytes(old);(S/'maintained/prepare.py').write_bytes(Path(__file__).read_bytes());put('maintained-inventory01.json',{p.name:pin(p)for p in (S/'maintained').iterdir()})
failedPrep=W/'mac-full-arithmetic45-execution227'
c['charged_roots'].append(str(failedPrep))
for p in failedPrep.rglob('*'):
 if p.is_file()and not p.is_symlink():c['static_records'][str(p)]=pin(p)
root=W/'mac-canonical-word215-source02';g=json.loads((root/'generation01.json').read_bytes());o=g['outputs'][0];require(pin(o['source']['path'])==o['source'],'exact generated source')
c['modules'][o['name']]=dict(source=o['source'],source_root=str(root/'source-root'),audits=o['audits'],imports=re.findall(r'^import ([\w.]+)\s*$',Path(o['source']['path']).read_text(),re.M))
c['charged_roots'].append(str(root))
for p in root.rglob('*'):
 if p.is_file():c['static_records'][str(p)]=pin(p)
order=[o['name']]+[n for n in c['order']if n not in c['qualified_batch_imports']and n!=o['name']]
require(len(order)==528,'exact remaining without replay')
available=set(c['qualified_batch_imports'])|set(json.loads(Path(c['closure']['path']).read_bytes())['modules'])
for n in order:
 for imported in c['modules'][n]['imports']:
  if imported.startswith('ShielddSecurity.'):require(imported.split('.',1)[1]in available,'custom dependency before '+n)
 available.add(n)
c.update(batch_root=str(S),maintained=str(S/'maintained'),own_cache=str(S/'own-cache'),runtime=str(S/'runtime'),carried_attempts=len(rs),carried_lean_seconds=sum(r['lean_seconds']for r in rs),carried_failure=pin(S/'protected-history01.json'),order=order)
c['charged_roots'].append(str(S));c['charged_roots']=list(dict.fromkeys(c['charged_roots']));c['lean_path'][0]=c['own_cache'];c['lean_environment']['LEAN_PATH']=':'.join(c['lean_path'])
(S/'dispatcher').mkdir();(S/'dispatcher/serial.py').write_bytes((P/'dispatcher/serial.py').read_bytes())
for p in [Path(__file__),Path('/tmp/stop_execution225_at_boundary.py'),S/'dispatcher/serial.py',*list((S/'maintained').iterdir())]:c['static_records'][str(p)]=pin(p)
closure=json.loads(Path(c['closure']['path']).read_bytes())['modules'];closure.update(c['qualified_batch_imports']);aliases={}
for n,d in closure.items():
 for suffix,v in d['current_slots'].items():
  if v is not None:aliases[str(S/'own-cache/ShielddSecurity'/(n+suffix))]=v
put('overlay-manifest01.json',dict(aliases=aliases,closure=c['closure']));c['overlay_manifest']=pin(S/'overlay-manifest01.json');put('config01.json',c)
put('transition-observation01.json',dict(scope='FAILED_CANONICAL_SOURCE01_ZERO_CREDIT',old_phase=str(P),ledger=pin(P/'runtime/ledger.jsonl'),checkpoint='Canonical215 failed Field Nat inference; explicit field parameter in maintained source02. Original entire failed module ZERO. Inactive217..225 metadata archived losslessly; only storage-map guard pin changed. All old sources/receipts/objects/logs/ledgers preserved.'))
put('plan01.json',dict(config=pin(S/'config01.json'),inventory=pin(S/'maintained-inventory01.json'),inherited=c['carried_failure'],remaining_named=len(order),new_names=[o['name']],guard_unchanged=pin(S/'maintained/guard.py'),no_accepted_replay=True,scope='Autonomous canonical word helper then remaining Boolean/word/hash/global coverage; unchanged per-run physical safeguards, no cumulative quota.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),preserved_inputs=c['carried_failure']));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),carried_attempts=len(rs),failures=126,first=order[:4],remaining=len(order),guard=pin(S/'maintained/guard.py'),producer=pin(S/'producer-manifest01.json'))))
