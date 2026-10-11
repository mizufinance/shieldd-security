from pathlib import Path
import json,hashlib,re,os
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');W=R/'work';PRE=W/'mac-full-arithmetic45-execution48';S=W/'mac-full-arithmetic45-execution49'
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
require(len(rs)==769 and sum(r['status']=='failed'for r in rs)==31 and all(r['cleanup']['clean']for r in rs),'exact historical769 attempts and thirtyone failures')
require(not S.exists(),'new immutable phase')
S.mkdir();entries={};links={}
for p in PRE.rglob('*'):
 if p.is_symlink():
  v=pin(p.resolve());entries[str(p)]=dict(path=str(p),symlink_target=os.readlink(p),target=v);links[str(p)]=v
 elif p.is_file():entries[str(p)]=pin(p)
# Retain only this phase alias delta; exact parent manifests carry prior aliases.
write('protected-history01.json',dict(parents=[c['carried_failure']],roots=[str(PRE)],entries=entries,historical_aliases=links,receipts=receipts,expected_statuses=[r['status']for r in rs],consumed_attempts=len(rs),consumed_lean_seconds=sum(r['lean_seconds']for r in rs)))
for rp,r in zip(receipts,rs):
 if r['status']!='passed':continue
 cache=Path(r['command'][r['command'].index('-o')+1]).parent;n=r['module']
 c['qualified_batch_imports'][n]=dict(source=r['source'],object=r['objects'][str(cache/(n+'.olean'))],receipt=rp,current_slots={suffix:r['objects'].get(str(cache/(n+suffix)))for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']},custom_imports=re.findall(r'^import (ShielddSecurity\.[\w.]+)\s*$',Path(r['source']['path']).read_text(),re.M),fresh_execution_credit=0,legacy_signature_inventory_absent=False)
(S/'maintained').mkdir();guard=(PRE/'maintained/guard.py').read_text()
require(guard.count('metadata<=512*1024*1024')==1 and guard.count("observation['metadata_bytes']<=508*1024*1024")==1,'unchanged disk-only finite metadata guard')
(S/'maintained/guard.py').write_text(guard);c['limits']['metadata_bytes']=512*1024*1024;(S/'maintained/prepare.py').write_bytes(Path(__file__).read_bytes());write('maintained-inventory01.json',{p.name:pin(p)for p in (S/'maintained').iterdir()})
semantic=[]
for dirname in ['mac-global-position77-source01']:
 root=W/dirname;generation=json.loads((root/'generation01.json').read_bytes());outputs=generation.get('outputs')
 if outputs is None:outputs=[dict(name='CapturedGlobalPosition77',source=generation['source'],audits=generation['audits'])]
 for g in outputs:
  name=g['name']
  if name=='TransferCore':continue
  require(pin(Path(g['source']['path']))==g['source'],'exact frozen semantic/generic source')
  require(name not in c['qualified_batch_imports'],'fresh module; no accepted replay')
  c['modules'][name]=dict(source=g['source'],source_root=str(root/'source-root'),audits=g['audits'],imports=re.findall(r'^import ([\w.]+)\s*$',Path(g['source']['path']).read_text(),re.M));semantic.append(name)
 for p in root.rglob('*'):
  if p.is_file():c['static_records'][str(p)]=pin(p)
 c['charged_roots'].append(str(root))
order=semantic
require(order==['CapturedGlobalPosition77'],'exact eight repaired/full/semantic successors')
c.update(batch_root=str(S),maintained=str(S/'maintained'),own_cache=str(S/'own-cache'),runtime=str(S/'runtime'),carried_attempts=len(rs),carried_lean_seconds=sum(r['lean_seconds']for r in rs),carried_failure=pin(S/'protected-history01.json'),order=order)
c['charged_roots'] += [str(W/'mac-first-epoch-nonzero61-source01'),str(W/'mac-first-epoch-nonzero61-source03'),str(W/'mac-full-arithmetic45-execution15'),str(W/'mac-first-epoch-hints62-source01'),str(W/'mac-first-epoch-hints62-source02'),str(W/'mac-first-epoch-hints62-source03'),str(W/'mac-first-epoch60-61-kernel-result01'),str(W/'mac-first-epoch-hints62-kernel-result01'),str(W/'mac-indexed-row-slice63-kernel-result01')];c['charged_roots'].append(str(S));c['charged_roots']=list(dict.fromkeys(c['charged_roots']));c['limits']['total_attempts']=len(rs)+220;c['limits']['aggregate_lean_seconds']=c['carried_lean_seconds']+1200;c['lean_path'][0]=c['own_cache'];c['lean_environment']['LEAN_PATH']=':'.join(c['lean_path'])
(S/'dispatcher').mkdir();(S/'dispatcher/serial.py').write_bytes((PRE/'dispatcher/serial.py').read_bytes())
for p in [Path(__file__),S/'dispatcher/serial.py',*list((S/'maintained').iterdir())]:c['static_records'][str(p)]=pin(p)
closure=json.loads(Path(c['closure']['path']).read_bytes())['modules'];closure.update(c['qualified_batch_imports']);aliases={}
for n,d in closure.items():
 for suffix,v in d['current_slots'].items():
  if v is not None:aliases[str(S/'own-cache/ShielddSecurity'/(n+suffix))]=v
write('overlay-manifest01.json',dict(aliases=aliases,closure=c['closure']));c['overlay_manifest']=pin(S/'overlay-manifest01.json');write('config01.json',c)
write('plan01.json',dict(config=pin(S/'config01.json'),inventory=pin(S/'maintained-inventory01.json'),inherited=c['carried_failure'],semantic_milestones=semantic,remaining_arithmetic_leaves=0,no_accepted_replay=True,all_physical_roots=c['charged_roots'],unchanged_physical_guards=True,scope='Fresh bounded semantic+arithmetic continuation, actual collected rows only. No legal-Transfer/native conclusion. Historical costs and every failure preserved.'))
write('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});write('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),preserved_inputs=c['carried_failure']));write('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),carried_attempts=len(rs),semantic=semantic,remaining=0)))
