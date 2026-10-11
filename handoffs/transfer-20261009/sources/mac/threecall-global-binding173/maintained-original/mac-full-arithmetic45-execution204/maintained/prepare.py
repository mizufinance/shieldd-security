from pathlib import Path
import json,hashlib,re,os,ast
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');W=R/'work';PRE=W/'mac-full-arithmetic45-execution203';S=W/'mac-full-arithmetic45-execution204'
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
def previous_config():
 path=PRE/'config01.json'
 if path.exists(): return path.read_bytes()
 import lzma
 record=json.loads((W/'mac-history-metadata-preservation126-18/archive-map01.json').read_bytes())['records'][str(path)]
 archive=record['archive'];require(pin(archive['path'])==archive,'exact previous archive')
 decoder=lzma.LZMADecompressor();raw=decoder.decompress(Path(archive['path']).read_bytes(),max_length=record['original']['bytes']+1)
 require(decoder.eof and not decoder.unused_data and len(raw)==record['original']['bytes'] and hashlib.sha256(raw).hexdigest()==record['original']['sha256'],'bounded exact previous config')
 return raw
c=json.loads(previous_config());history=json.loads(Path(c['carried_failure']['path']).read_bytes());receipts=history['receipts']+[pin(p)for p in sorted((PRE/'runtime/receipts').glob('*.json'))];rs=[json.loads(Path(p['path']).read_bytes())for p in receipts]
require(len(rs)==1026 and sum(r['status']=='failed'for r in rs)==114 and all(r['cleanup']['clean']for r in rs),'exact historical777 attempts and thirtythree failures')
require(not S.exists(),'new immutable phase')
S.mkdir();entries={};links={}
for p in PRE.rglob('*'):
 if p.is_symlink():
  v=pin(p.resolve());entries[str(p)]=dict(path=str(p),symlink_target=os.readlink(p),target=v);links[str(p)]=v
 elif p.is_file():entries[str(p)]=pin(p)
storage=json.loads((W/'mac-history-metadata-preservation126-18/archive-map01.json').read_bytes())['records']
for key,record in storage.items():
 if Path(key).is_relative_to(PRE):entries[key]=record['original']
# Retain only this phase alias delta; exact parent manifests carry prior aliases.
write('protected-history01.json',dict(parents=[c['carried_failure']],roots=[str(PRE)],entries=entries,historical_aliases=links,receipts=receipts,expected_statuses=[r['status']for r in rs],consumed_attempts=len(rs),consumed_lean_seconds=sum(r['lean_seconds']for r in rs)))
for rp,r in zip(receipts,rs):
 if r['status']!='passed':continue
 cache=Path(r['command'][r['command'].index('-o')+1]).parent;n=r['module']
 c['qualified_batch_imports'][n]=dict(source=r['source'],object=r['objects'][str(cache/(n+'.olean'))],receipt=rp,current_slots={suffix:r['objects'].get(str(cache/(n+suffix)))for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']},custom_imports=re.findall(r'^import (ShielddSecurity\.[\w.]+)\s*$',Path(r['source']['path']).read_text(),re.M),fresh_execution_credit=0,legacy_signature_inventory_absent=False)
(S/'maintained').mkdir();guard=(PRE/'maintained/guard.py').read_text()
a=guard.index('_STORAGE_PIN = ');b=guard.index('\n_STORAGE =',a);guard=guard[:a]+'_STORAGE_PIN = '+repr(pin(W/'mac-history-metadata-preservation126-18/archive-map01.json'))+guard[b:]
addition_path=str(W/'mac-full-arithmetic45-execution186/config01.json')
addition=storage[addition_path]['original']
c['history_closed_keyset_additions']={addition_path:addition}
require(guard.count('metadata<=1024*1024*1024')==1 and guard.count("observation['metadata_bytes']<=1020*1024*1024")==1,'unchanged disk-only finite metadata guard')
guard=guard.replace('metadata<=768*1024*1024','metadata<=1024*1024*1024').replace("observation['metadata_bytes']<=764*1024*1024","observation['metadata_bytes']<=1020*1024*1024");# Same complete bytes/keyset/pin checks, one decoded history node at a time.
ast.parse(guard)
(S/'maintained/guard.py').write_text(guard);c['limits']['metadata_bytes']=1024*1024*1024;(S/'maintained/prepare.py').write_bytes(Path(__file__).read_bytes());write('maintained-inventory01.json',{p.name:pin(p)for p in (S/'maintained').iterdir()})
semantic=[]
for dirname in ['mac-merkle-global-body181-source02','mac-merkle-global-pilot182-source02','mac-threecall-global-binding173-source09','mac-registry-global-binding175-source02','mac-registry-global-sound176-source01']:
 root=W/dirname;generation=json.loads((root/'generation01.json').read_bytes());outputs=generation.get('outputs')
 if outputs is None:outputs=[dict(name='CapturedValueGlobal108',source=generation['source'],audits=generation['audits'])]
 for g in outputs:
  name=g['name']
  if name=='TransferCore' or name in c['qualified_batch_imports']:continue
  require(pin(Path(g['source']['path']))==g['source'],'exact frozen semantic/generic source')
  require(name not in c['qualified_batch_imports'],'fresh module; no accepted replay')
  c['modules'][name]=dict(source=g['source'],source_root=str(root/'source-root'),audits=g['audits'],imports=re.findall(r'^import ([\w.]+)\s*$',Path(g['source']['path']).read_text(),re.M));semantic.append(name)
 for p in root.rglob('*'):
  if p.is_file():c['static_records'][str(p)]=pin(p)
 c['charged_roots'].append(str(root))
officialRoot=W/'mac-subgroup-official56-data01'
c['official']=pin(officialRoot/'official-union01.json')
c['charged_roots'].append(str(officialRoot))
for root in [officialRoot,W/'mac-full-arithmetic45-execution54',W/'mac-full-arithmetic45-execution55']:
 for p in root.rglob('*'):
  if p.is_file() and not p.is_symlink(): c['static_records'][str(p)]=pin(p)
refusedRoot=W/'mac-full-arithmetic45-execution94'
c['charged_roots'].append(str(refusedRoot))
for p in refusedRoot.rglob('*'):
 if p.is_file():c['static_records'][str(p)]=pin(p)
for unusedRoot in [W/'mac-threecall-global-binding173-source08',W/'mac-merkle-global-body181-kernel-result01',W/'mac-threecall-global-binding173-source07',W/'mac-merkle-global-body181-source01',W/'mac-merkle-global-pilot182-source01',W/'mac-history-metadata-preservation126-18',W/'mac-threecall-global-binding173-source06',W/'mac-threecall-global-binding173-source05',W/'mac-prior-global170-kernel-result01',W/'mac-prior-global-binding170-source05',W/'mac-indexed-coverage172-174-178-179-kernel-result01',W/'mac-indexed-copy-constant178-source01',W/'mac-call04-global168-169-kernel-result01',W/'mac-exact-pack-pilot179-source01',W/'mac-registry-global-binding175-source01',W/'mac-registry-global-sound176-source01',W/'mac-threecall-global-binding173-source02',W/'mac-indexed-copy-collection174-source01',W/'mac-prior-global-binding170-source04',W/'mac-threecall-global-binding173-source03',W/'mac-call04-global-binding168-source06',W/'mac-prior-global-binding170-source03',W/'mac-selected-chunks172-source01',W/'mac-selected-chunks172-source02',W/'mac-selected-chunks172-source03',W/'mac-threecall-global-binding173-source01',W/'mac-indexed-copy-stream171-kernel-result01',W/'mac-call04-global-binding168-source05',W/'mac-prior-global-binding170-source02',W/'mac-indexed-copy-stream171-source01',W/'mac-call04-global-binding168-source04',W/'mac-call04-global-binding168-source03',W/'mac-first-hash-global-sound169-source01',W/'mac-prior-global-binding170-source01',W/'mac-call04-global-binding168-source02',W/'mac-history-metadata-preservation126-16',W/'mac-call04-global-binding168-source01',W/'mac-anchor-indexed165-166-kernel-result01',W/'mac-history-metadata-preservation126-15',W/'mac-history-metadata-preservation126-18',W/'mac-indexed-copy-selection166-source02',W/'mac-history-metadata-preservation126-14',W/'mac-indexed-copy-selection166-source01',W/'mac-anchor-row-sound165-source01',W/'mac-regulated-sound163-source01',W/'mac-registry-numbers164-source01',W/'mac-registry-canonical-order160-164-kernel-result01',W/'mac-asset-decode160-source02',W/'mac-next-decode161-source02',W/'mac-registry-order-sound162-source01',W/'mac-asset-decode160-source01',W/'mac-next-decode161-source01',W/'mac-canonical-decode157-159-kernel-result01',W/'mac-history-metadata-preservation126-13',W/'mac-value-decode158-source03',W/'mac-selected-comparison-sound159-source01',W/'mac-value-decode158-source02',W/'mac-value-decode158-source01',W/'mac-value-canonical-sound157-source02',W/'mac-gap-sound153-156-kernel-result01',W/'mac-value-canonical-sound157-source01',W/'mac-registry-gap-sound156-source02',W/'mac-registry-gap-sound156-source01',W/'mac-zero-flag-sound155-source02',W/'mac-zero-flag-sound155-source01',W/'mac-comparison-sound148-152-kernel-result01',W/'mac-full-comparison152-source02',W/'mac-next-high-sound153-source01',W/'mac-next-low-sound154-source01',W/'mac-history-metadata-preservation126-12',W/'mac-full-comparison152-source01',W/'mac-boolean-decode150-source03',W/'mac-low-comparison-sound151-source01',W/'mac-boolean-decode150-source02',W/'mac-high-comparison-sound149-source02',W/'mac-boolean-decode150-source01',W/'mac-high-comparison-sound149-source01',W/'mac-comparison-sound148-source03',W/'mac-comparison-sound148-source02',W/'mac-comparison-sound148-source01',W/'mac-registry-gap145-147-kernel-result01',W/'mac-registry-gap145-source03',W/'mac-history-metadata-preservation126-11',W/'mac-registry-gap145-source02',W/'mac-next-high-low133-144-kernel-result01',W/'mac-registry-gap145-source01',W/'mac-registry-gap146-source01',W/'mac-registry-gap146-source02',W/'mac-lexicographic-comparison144-source04',W/'mac-lexicographic-comparison144-source03',W/'mac-lexicographic-comparison144-source02',W/'mac-registry-gap145-data01',W/'mac-lexicographic-comparison144-source01',W/'mac-next-low-limb140-data01',W/'mac-next-high-zero-shared139-source01',W/'mac-next-high-zero138-source01',W/'mac-next-high-zero137-data01',W/'mac-next-high-shared136-source01',W/'mac-low-limb129-132-kernel-result01',W/'mac-next-high-limb133-source01',W/'mac-next-high-limb133-data01',W/'mac-high-zero125-128-kernel-result01',W/'mac-registry-low-limb129-data01',W/'mac-low-bit-meaning128-source01',W/'mac-high-zero-shared127-source01',W/'mac-registry-high-zero126-data-source05',W/'mac-registry-high-zero126-source08',W/'mac-registry-high-zero126-data-source04',W/'mac-history-metadata-preservation126-09',W/'mac-history-metadata-preservation126-10',W/'mac-inactive-cache-preservation126-08',W/'mac-registry-high-zero126-source02',W/'mac-inactive-cache-preservation126-06',W/'mac-inactive-cache-preservation126-07',W/'mac-registry-high-zero126-source01',W/'mac-inactive-cache-preservation126-01',W/'mac-inactive-cache-preservation126-02',W/'mac-inactive-cache-preservation126-03',W/'mac-inactive-cache-preservation126-04',W/'mac-inactive-cache-preservation126-05',W/'mac-field-zero-seed125-source01',W/'mac-registry-high-zero126-data01',W/'mac-high-limb119-124-kernel-result01',W/'mac-inactive-cache-preservation123-01',W/'mac-high-limb-global123-source01',W/'mac-high-bit-meaning122-source01',W/'mac-inactive-cache-preservation120-02',W/'mac-registry-high-limb120-source02',W/'mac-registry-high-limb121-source01',W/'mac-registry-high-limb121-source02',W/'mac-inactive-cache-preservation120-01',W/'mac-registry-high-limb120-source01',W/'mac-bounded-limb-comparison119-source03',W/'mac-registry-high-limb120-data01',W/'mac-registry-high-limb120-data02',W/'mac-bounded-limb-comparison119-source02',W/'mac-inactive-cache-preservation115-05',W/'mac-bounded-limb-comparison119-source01',W/'mac-next-canonical114-118-kernel-result01',W/'mac-next-comparison116-root-source01',W/'mac-next-global118-source01',W/'mac-inactive-cache-preservation115-01',W/'mac-inactive-cache-preservation115-02',W/'mac-inactive-cache-preservation115-03',W/'mac-inactive-cache-preservation115-04',W/'mac-next-comparison115-data01',W/'mac-inactive-cache-preservation110-04',W/'mac-inactive-cache-preservation110-05',W/'mac-asset-canonical109-113-kernel-result01',W/'mac-inactive-cache-preservation110-01',W/'mac-inactive-cache-preservation110-02',W/'mac-inactive-cache-preservation110-03',W/'mac-asset-comparison110-transport-source01',W/'mac-asset-comparison110-data01',W/'mac-registry-asset-range109-source01',W/'mac-full-arithmetic45-execution112',W/'mac-comparison-certificate101-source01']:
 c['charged_roots'].append(str(unusedRoot))
 for p in unusedRoot.rglob('*'):
  if p.is_file():c['static_records'][str(p)]=pin(p)
order=[n for n in semantic if n!='CapturedMerkleGlobalPilot182']+['CapturedMerkleGlobalPilot182']
require(len(order)==94 and order[0]=='CapturedThreeCallGlobalBinding173H000','separate16-row leaf topology')
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
