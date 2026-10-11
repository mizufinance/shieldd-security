from pathlib import Path
import json,hashlib,re,os
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');OLD=R/'work/mac-full-arithmetic45-source01';PRE=R/'work/mac-full-arithmetic45-execution03';S=R/'work/mac-full-arithmetic45-execution04'
def require(ok,reason):
 if not ok:raise ValueError(reason)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def write(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
pc=json.loads((PRE/'config01.json').read_bytes());history=json.loads(Path(pc['carried_failure']['path']).read_bytes());receipts=history['receipts']+[pin(p)for p in sorted((PRE/'runtime/receipts').glob('*.json'))];rs=[json.loads(Path(p['path']).read_bytes())for p in receipts]
require(len(rs)==15 and [r['status'] for r in rs]==['passed']*8+['failed']*2+['passed']*5 and all(r['cleanup']['clean']for r in rs),'twelve leaves, two preserved failed repairs and passed composition')
S.mkdir();c=pc;full=json.loads((OLD/'config01.json').read_bytes());entries={};links={}
for p in PRE.rglob('*'):
 if p.is_symlink():
  v=pin(p.resolve());entries[str(p)]=dict(path=str(p),symlink_target=os.readlink(p),target=v);links[str(p)]=v
 elif p.is_file():entries[str(p)]=pin(p)
def merged_aliases(h):
 result={}
 for parent in h.get('parents',[]):result.update(merged_aliases(json.loads(Path(parent['path']).read_bytes())))
 result.update(h.get('historical_aliases',{}));return result
links={**merged_aliases(history),**links}
write('protected-history01.json',dict(parents=[c['carried_failure']],roots=[str(PRE)],entries=entries,historical_aliases=links,receipts=receipts,expected_statuses=[r['status']for r in rs],consumed_attempts=len(rs),consumed_lean_seconds=sum(r['lean_seconds']for r in rs)))
for rp,r in zip(receipts,rs):
 if r['status']!='passed':continue
 cache=Path(r['command'][r['command'].index('-o')+1]).parent
 n=r['module'];c['qualified_batch_imports'][n]=dict(source=r['source'],object=r['objects'][str(cache/(n+'.olean'))],receipt=rp,current_slots={suffix:r['objects'].get(str(cache/(n+suffix)))for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']},custom_imports=re.findall(r'^import (ShielddSecurity\.[\w.]+)\s*$',Path(r['source']['path']).read_text(),re.M),fresh_execution_credit=0,legacy_signature_inventory_absent=False)
(S/'maintained').mkdir();guard=(PRE/'maintained/guard.py').read_text()
old='def direct_imports(data):'
require(guard.count(old)==1,'exact header parser context')
guard=guard.replace(old,'def uncached_direct_imports(data):')
marker='def official_header(data):'
cache="""# Pure parsing memoization by exact byte digest within this single guard process.
# Every source is still read and SHA checked at every fixed_check phase.
_IMPORT_HEADERS={}
def direct_imports(data):
    digest=sha(data)
    if digest not in _IMPORT_HEADERS:
        _IMPORT_HEADERS[digest]=tuple(uncached_direct_imports(data))
    return list(_IMPORT_HEADERS[digest])

"""
require(guard.count(marker)==1,'exact header cache insertion')
guard=guard.replace(marker,cache+marker)
(S/'maintained/guard.py').write_text(guard);(S/'maintained/prepare.py').write_bytes(Path(__file__).read_bytes());write('maintained-inventory01.json',{p.name:pin(p)for p in (S/'maintained').iterdir()})
c.update(batch_root=str(S),maintained=str(S/'maintained'),own_cache=str(S/'own-cache'),runtime=str(S/'runtime'),carried_attempts=len(rs),carried_lean_seconds=sum(r['lean_seconds']for r in rs),carried_failure=pin(S/'protected-history01.json'),charged_roots=pc['charged_roots']+[str(S)])
c['order']=c['order'][4:];c['modules']=full['modules'];c['source_root']=full['source_root'];c['limits']=full['limits'];c['lean_path'][0]=c['own_cache'];c['lean_environment']['LEAN_PATH']=':'.join(c['lean_path'])
for p in [Path(__file__),*list((S/'maintained').iterdir())]:c['static_records'][str(p)]=pin(p)
closure=json.loads(Path(c['closure']['path']).read_bytes())['modules'];closure.update(c['qualified_batch_imports']);aliases={}
for n,d in closure.items():
 for suffix,v in d['current_slots'].items():
  if v is not None:aliases[str(S/'own-cache/ShielddSecurity'/(n+suffix))]=v
write('overlay-manifest01.json',dict(aliases=aliases,closure=c['closure']));c['overlay_manifest']=pin(S/'overlay-manifest01.json');write('config01.json',c)
write('plan01.json',dict(config=pin(S/'config01.json'),inventory=pin(S/'maintained-inventory01.json'),unchanged_source_root=c['source_root'],all_generated_source_hashes_still_checked_every_phase=True,lexical_feature_and_audit_guard='Applied to exact ACTIVE own module before every dispatch; inactive unimported future leaves remain byte-pinned, are lexically checked when dispatched. No bypass for executing source.',inherited_custom_and_official_checks='UNCHANGED complete import/root/source/object/companion checks',previous_eight_results=receipts[:8],separate_composition_attempts=receipts[8:11],representative_results=receipts[11:],import_parser_cache='Pure direct-header parse results by SHA of current bytes; all sources/objects/receipts still read and exact hashes checked pre/post. No persistent cache or skipped identity check.',no_replay=True,safety_limits_unchanged=True,all_physical_roots=c['charged_roots'],aggregate_lean_seconds_used=c['carried_lean_seconds'],sourcecopy_bytes=0))
write('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});write('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),preserved_inputs=c['carried_failure']));write('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(dict(stage=str(S),carry_attempts=len(rs),carry_seconds=c['carried_lean_seconds'],next=c['order'][0])))
