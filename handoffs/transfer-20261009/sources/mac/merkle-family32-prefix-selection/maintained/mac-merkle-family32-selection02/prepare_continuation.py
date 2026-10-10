"""Finite immutable endpoint continuation; preserve every old result, no launch."""
from pathlib import Path
import json,hashlib,os,re
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');S=Path(__file__).resolve().parent;PRE=R/'work/mac-merkle-family32-selection01'
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def write(p,d):
 with p.open('x') as f:f.write(json.dumps(d,sort_keys=True,separators=(',',':'))+'\n')
c=json.loads((PRE/'config01.json').read_bytes());old=json.loads(Path(c['carried_failure']['path']).read_bytes());roots=[str(PRE)];entries={};links={}
for r in roots:
 for p in Path(r).rglob('*'):
  if p.is_symlink():
   t=pin(p.resolve());entries[str(p)]=dict(path=str(p),symlink_target=os.readlink(p),target=t);links[str(p)]=t
  elif p.is_file():entries[str(p)]=pin(p)
receipts=old['receipts']+[pin(p) for p in sorted((PRE/'runtime/receipts').glob('*.json'))];rs=[json.loads(Path(p['path']).read_bytes()) for p in receipts]
h=dict(parents=[c['carried_failure']],roots=roots,entries=entries,historical_aliases=links,receipts=receipts,expected_statuses=[r['status'] for r in rs],consumed_attempts=len(rs),consumed_lean_seconds=sum(r['lean_seconds'] for r in rs));write(S/'protected-history01.json',h)
for rp in sorted((PRE/'runtime/receipts').glob('*.json')):
 d=json.loads(rp.read_bytes())
 if d['status']!='passed':continue
 name=d['module'];o=d['objects'][str(PRE/'own-cache/ShielddSecurity'/(name+'.olean'))];c['qualified_batch_imports'][name]=dict(source=d['source'],object=o,receipt=pin(rp),current_slots={suffix:d['objects'].get(str(PRE/'own-cache/ShielddSecurity'/(name+suffix))) for suffix in ('.olean','.olean.private','.olean.server','.ilean','.ir')},custom_imports=re.findall(r'^import (ShielddSecurity\.[\w.]+)\s*$',Path(d['source']['path']).read_text(),re.M),fresh_execution_credit=0,legacy_signature_inventory_absent=False)
(S/'maintained').mkdir();(S/'maintained/guard.py').write_bytes((S/'reviewed-guard-input.py').read_bytes());(S/'maintained/prepare.py').write_text('"""Immutable finite continuation metadata only."""\n');mi={p.name:pin(p) for p in (S/'maintained').iterdir()};write(S/'maintained-inventory01.json',mi)
c.update(schema='Initial734-row-match-leaves-continuation03',batch_root=str(S),maintained=str(S/'maintained'),source_root=str(S/'source-root'),own_cache=str(S/'own-cache'),runtime=str(S/'runtime'),carried_attempts=len(rs),carried_lean_seconds=h['consumed_lean_seconds'],carried_failure=pin(S/'protected-history01.json'),charged_roots=c['charged_roots']+[str(S)])
c['order']=['MerkleFamily32Selection']
c['modules']={}
for n in c['order']:
 if n not in c['modules']:c['modules'][n]={'audits':re.findall(r'^#check @([\w.]+)',(S/'source-root/ShielddSecurity'/(n+'.lean')).read_text(),re.M)}
for n,d in c['modules'].items():
 p=S/'source-root/ShielddSecurity'/(n+'.lean');d['source']=pin(p);actual=re.findall(r'^#check @([\w.]+)',p.read_text(),re.M);require(set(actual)==set(d['audits']),'exact planned named audits');d['audits']=actual;d['imports']=re.findall(r'^import ([\w.]+)\s*$',p.read_text(),re.M)
c['charged_roots']=[str(S)];c['limits']['total_attempts']=len(rs)+16;c['limits']['aggregate_lean_seconds']=h['consumed_lean_seconds']+1200;c['lean_path'][0]=c['own_cache'];c['lean_environment']['LEAN_PATH']=':'.join(c['lean_path'])
for p in list((S/'maintained').iterdir())+[Path(__file__),S/'generate.py',S/'selection-template.lean.txt']:c['static_records'][str(p)]=pin(p)
closure=json.loads(Path(c['closure']['path']).read_bytes())['modules'];closure.update(c['qualified_batch_imports']);aliases={}
for n,d in closure.items():
 for suffix,identity in d['current_slots'].items():
  if identity is not None:aliases[str(S/'own-cache/ShielddSecurity'/(n+suffix))]=identity
write(S/'overlay-manifest01.json',dict(aliases=aliases,closure=c['closure']));c['overlay_manifest']=pin(S/'overlay-manifest01.json');write(S/'config01.json',c)
write(S/'plan01.json',dict(config=pin(S/'config01.json'),inventory=pin(S/'maintained-inventory01.json'),order=c['order'],carried_attempts=len(rs),carried_seconds=h['consumed_lean_seconds'],new_task_all_attempt_limit=8,absolute_limit=c['limits']['total_attempts'],qualified_imports=len(closure),qualified_replayed=0,source_delta='Second actual asset path level:40 arithmetic prefix rows3158..3197, independently qualified raw operations/certificates/ports/stream; generic unconditional phase construction and independent round semantics. Full16levels/anchor/fullrelationremainopen.'))
write(S/'producer-manifest01.json',{str(p.relative_to(S)):pin(p) for p in S.rglob('*') if p.is_file()});write(S/'envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),previous_history=c['carried_failure'],scope='Immutable maintained repair; no claimed new result before accepted receipt.'));write(S/'postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json'),protected_paths=len(entries)))
print(json.dumps({'stage':str(S),'carry_attempts':len(rs),'carry_seconds':h['consumed_lean_seconds']}))
