from pathlib import Path
import json,hashlib,re,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');PRE=W/'mac-assertion-provider50-execution09';S=W/'mac-assertion-provider50-execution10'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def write(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
c=json.loads((PRE/'config01.json').read_bytes());h=json.loads(Path(c['carried_failure']['path']).read_bytes());rps=h['receipts']+[pin(p)for p in sorted((PRE/'runtime/receipts').glob('*.json'))];rs=[json.loads(Path(p['path']).read_bytes())for p in rps]
require(len(rs)==394 and sum(r['status']=='failed'for r in rs)==13 and all(r['cleanup']['clean']for r in rs),'exact retained394 attempts and clean cleanup')
S.mkdir();entries={};links={}
for p in PRE.rglob('*'):
 if p.is_symlink():
  v=pin(p.resolve());entries[str(p)]=dict(path=str(p),symlink_target=os.readlink(p),target=v);links[str(p)]=v
 elif p.is_file():entries[str(p)]=pin(p)
def aliases(h):
 d={}
 for v in h.get('parents',[]):d.update(aliases(json.loads(Path(v['path']).read_bytes())))
 d.update(h.get('historical_aliases',{}));return d
write('protected-history01.json',dict(parents=[c['carried_failure']],roots=[str(PRE)],entries=entries,historical_aliases={**aliases(h),**links},receipts=rps,expected_statuses=[r['status']for r in rs],consumed_attempts=len(rs),consumed_lean_seconds=sum(r['lean_seconds']for r in rs)))
for rp,r in zip(rps,rs):
 if r['status']!='passed':continue
 n=r['module'];cache=Path(r['command'][r['command'].index('-o')+1]).parent
 c['qualified_batch_imports'][n]=dict(source=r['source'],object=r['objects'][str(cache/(n+'.olean'))],receipt=rp,current_slots={s:r['objects'].get(str(cache/(n+s)))for s in ['.olean','.olean.private','.olean.server','.ilean','.ir']},custom_imports=re.findall(r'^import (ShielddSecurity\.[\w.]+)\s*$',Path(r['source']['path']).read_text(),re.M),fresh_execution_credit=0,legacy_signature_inventory_absent=False)
(S/'maintained').mkdir();(S/'maintained/guard.py').write_bytes((PRE/'maintained/guard.py').read_bytes());(S/'maintained/prepare.py').write_bytes(Path(__file__).read_bytes());write('maintained-inventory01.json',{p.name:pin(p)for p in (S/'maintained').iterdir()})
passed={r['module']for r in rs if r['status']=='passed'};c['order']=[n for n in c['order']if n not in passed];require(len(c['order'])==6,'only four remaining groups/root/links')
root=W/'mac-assertion-links57-source02';v=json.loads((root/'generation01.json').read_bytes());c['modules'][v['name']]=dict(source=v['source'],source_root=str(root/'source-root'),audits=v['audits'],imports=re.findall(r'^import ([\w.]+)\s*$',Path(v['source']['path']).read_text(),re.M))
for p in root.rglob('*'):
 if p.is_file():c['static_records'][str(p)]=pin(p)
c.update(batch_root=str(S),maintained=str(S/'maintained'),own_cache=str(S/'own-cache'),runtime=str(S/'runtime'),carried_attempts=len(rs),carried_lean_seconds=sum(r['lean_seconds']for r in rs),carried_failure=pin(S/'protected-history01.json'),charged_roots=list(dict.fromkeys(c['charged_roots']+[str(S),str(root)])))
c['limits']['total_attempts']=len(rs)+16;c['limits']['aggregate_lean_seconds']=c['carried_lean_seconds']+180;c['lean_path'][0]=c['own_cache'];c['lean_environment']['LEAN_PATH']=':'.join(c['lean_path'])
(S/'dispatcher').mkdir();(S/'dispatcher/serial.py').write_bytes((PRE/'dispatcher/serial.py').read_bytes())
for p in [Path(__file__),S/'dispatcher/serial.py',*list((S/'maintained').iterdir())]:c['static_records'][str(p)]=pin(p)
closure=json.loads(Path(c['closure']['path']).read_bytes())['modules'];closure.update(c['qualified_batch_imports']);aa={}
for n,d in closure.items():
 for suffix,v in d['current_slots'].items():
  if v is not None:aa[str(S/'own-cache/ShielddSecurity'/(n+suffix))]=v
write('overlay-manifest01.json',dict(aliases=aa,closure=c['closure']));c['overlay_manifest']=pin(S/'overlay-manifest01.json');write('config01.json',c)
write('plan01.json',dict(config=pin(S/'config01.json'),inventory=pin(S/'maintained-inventory01.json'),order=c['order'],carry_attempts=len(rs),carry_seconds=c['carried_lean_seconds'],guard_byte_identical=pin(PRE/'maintained/guard.py')['sha256']==pin(S/'maintained/guard.py')['sha256'],scope='Complete assertion provider aggregate and verifier-link join; no accepted module replay, no legal-input truth premise.',limits=c['limits'],historical_failure_credit=0))
write('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});write('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),preserved_inputs=c['carried_failure']));write('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),order=c['order'],attempts=len(rs),seconds=c['carried_lean_seconds'])))
