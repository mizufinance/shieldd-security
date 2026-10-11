from pathlib import Path
import json,hashlib,re,os
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');W=R/'work';PRE=W/'mac-full-arithmetic45-execution13';S=W/'mac-full-arithmetic45-execution14'
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def write(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
def merged_aliases(h):
 result={}
 for parent in h.get('parents',[]):result.update(merged_aliases(json.loads(Path(parent['path']).read_bytes())))
 result.update(h.get('historical_aliases',{}));return result
c=json.loads((PRE/'config01.json').read_bytes());history=json.loads(Path(c['carried_failure']['path']).read_bytes());receipts=history['receipts']+[pin(p)for p in sorted((PRE/'runtime/receipts').glob('*.json'))];rs=[json.loads(Path(p['path']).read_bytes())for p in receipts]
require(len(rs)==529 and sum(r['status']=='failed'for r in rs)==14 and all(r['cleanup']['clean']for r in rs),'exact historical529 attempts and fourteen failures')
require(not S.exists(),'new immutable phase')
S.mkdir();entries={};links={}
for p in PRE.rglob('*'):
 if p.is_symlink():
  v=pin(p.resolve());entries[str(p)]=dict(path=str(p),symlink_target=os.readlink(p),target=v);links[str(p)]=v
 elif p.is_file():entries[str(p)]=pin(p)
links={**merged_aliases(history),**links}
write('protected-history01.json',dict(parents=[c['carried_failure']],roots=[str(PRE)],entries=entries,historical_aliases=links,receipts=receipts,expected_statuses=[r['status']for r in rs],consumed_attempts=len(rs),consumed_lean_seconds=sum(r['lean_seconds']for r in rs)))
for rp,r in zip(receipts,rs):
 if r['status']!='passed':continue
 cache=Path(r['command'][r['command'].index('-o')+1]).parent;n=r['module']
 c['qualified_batch_imports'][n]=dict(source=r['source'],object=r['objects'][str(cache/(n+'.olean'))],receipt=rp,current_slots={suffix:r['objects'].get(str(cache/(n+suffix)))for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']},custom_imports=re.findall(r'^import (ShielddSecurity\.[\w.]+)\s*$',Path(r['source']['path']).read_text(),re.M),fresh_execution_credit=0,legacy_signature_inventory_absent=False)
(S/'maintained').mkdir();(S/'maintained/guard.py').write_bytes((PRE/'maintained/guard.py').read_bytes());(S/'maintained/prepare.py').write_bytes(Path(__file__).read_bytes());write('maintained-inventory01.json',{p.name:pin(p)for p in (S/'maintained').iterdir()})
passed={r['module']for r in rs if r['status']=='passed'};future=[n for n in c['order']if n.startswith('CapturedArithmetic45') and n not in passed];require(len(future)==195,'exact remaining195 production leaves')
semantic=[]
for stage,name in [('mac-first-epoch-range60-source02','CapturedEpochRange60'),('mac-first-epoch-nonzero61-source02','CapturedEpochNonzero61')]:
 root=W/stage;g=json.loads((root/'generation01.json').read_bytes());require(pin(Path(g['source']['path']))==g['source'],'frozen semantic source')
 c['modules'][name]=dict(source=g['source'],source_root=str(root/'source-root'),audits=g['audits'],imports=re.findall(r'^import (ShielddSecurity\.[\w.]+)\s*$',Path(g['source']['path']).read_text(),re.M));semantic.append(name)
 for p in root.rglob('*'):
  if p.is_file():c['static_records'][str(p)]=pin(p)
 c['charged_roots'].append(str(root))
c.update(batch_root=str(S),maintained=str(S/'maintained'),own_cache=str(S/'own-cache'),runtime=str(S/'runtime'),carried_attempts=len(rs),carried_lean_seconds=sum(r['lean_seconds']for r in rs),carried_failure=pin(S/'protected-history01.json'),order=semantic+future)
c['charged_roots'].append(str(W/'mac-first-epoch-nonzero61-source01'));c['charged_roots'].append(str(S));c['charged_roots']=list(dict.fromkeys(c['charged_roots']));c['limits']['total_attempts']=len(rs)+220;c['limits']['aggregate_lean_seconds']=c['carried_lean_seconds']+1200;c['lean_path'][0]=c['own_cache'];c['lean_environment']['LEAN_PATH']=':'.join(c['lean_path'])
(S/'dispatcher').mkdir();(S/'dispatcher/serial.py').write_bytes((PRE/'dispatcher/serial.py').read_bytes())
for p in [Path(__file__),S/'dispatcher/serial.py',*list((S/'maintained').iterdir())]:c['static_records'][str(p)]=pin(p)
closure=json.loads(Path(c['closure']['path']).read_bytes())['modules'];closure.update(c['qualified_batch_imports']);aliases={}
for n,d in closure.items():
 for suffix,v in d['current_slots'].items():
  if v is not None:aliases[str(S/'own-cache/ShielddSecurity'/(n+suffix))]=v
write('overlay-manifest01.json',dict(aliases=aliases,closure=c['closure']));c['overlay_manifest']=pin(S/'overlay-manifest01.json');write('config01.json',c)
write('plan01.json',dict(config=pin(S/'config01.json'),inventory=pin(S/'maintained-inventory01.json'),inherited=c['carried_failure'],semantic_first=semantic,remaining_arithmetic_leaves=195,no_accepted_replay=True,all_physical_roots=c['charged_roots'],unchanged_physical_guards=True,scope='Fresh bounded semantic+arithmetic continuation, actual collected rows only. No legal-Transfer/native conclusion. Historical costs and every failure preserved.'))
write('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});write('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),preserved_inputs=c['carried_failure']));write('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),carried_attempts=len(rs),semantic=semantic,remaining=len(future))))
