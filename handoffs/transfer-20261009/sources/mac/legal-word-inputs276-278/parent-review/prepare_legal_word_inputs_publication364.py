from pathlib import Path
import json,hashlib,zlib,shutil,importlib.util
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/mac/legal-word-inputs276-278';assert not (D/'publication-manifest01.json').exists()
spec=importlib.util.spec_from_file_location('preserved',J/'read_preserved_mac_config20.py');preserved=importlib.util.module_from_spec(spec);spec.loader.exec_module(preserved)
sha=lambda b:hashlib.sha256(b).hexdigest();records=[];refs=[];seen={};old={}
for p in(G/'handoffs/transfer-20261009/sources/mac').glob('*/original-byte-map01.json'):
 for e in json.loads(p.read_text())['files']:old.setdefault(e['original']['sha256'],(p.parent,e))
def read(p):
 p=Path(p);return p.read_bytes()if p.exists()else preserved.read_original(p)
def copy(p,n,prior=False):
 p=Path(p);b=read(p);o=dict(path=str(p),bytes=len(b),sha256=sha(b))
 if prior and o['sha256']in old:
  base,e=old[o['sha256']];q=base/e['publication']['path'];encoded=q.read_bytes();assert len(encoded)==e['publication']['bytes']and sha(encoded)==e['publication']['sha256'];assert(zlib.decompress(encoded)if e.get('encoding')=='zlib'else encoded)==b
  refs.append(dict(original=o,prior_publication=str(q.relative_to(G)),encoding=e.get('encoding','identity')));return
 if o['sha256']in seen:
  records.append(dict(original=o,**seen[o['sha256']]));return
 compressed=p.suffix=='.json'and len(b)>262144;enc=zlib.compress(b,1)if compressed else b
 if compressed:n=Path(str(n)+'.zlib')
 assert shutil.disk_usage(W).free>2147483648+4*1024*1024+len(enc)
 q=D/n;q.parent.mkdir(parents=True,exist_ok=True);(q.write_bytes(enc) if not q.exists() else None);assert(zlib.decompress(q.read_bytes())if compressed else q.read_bytes())==b
 pub=dict(publication=dict(path=str(q.relative_to(D)),bytes=len(enc),sha256=sha(enc)),encoding='zlib'if compressed else'identity');seen[o['sha256']]=pub;records.append(dict(original=o,**pub))
tasks=[('legal-word-inputs276-278','mac-legal-word-inputs276-278-kernel-result01',2,22)];mods=[];all_audits=[];roots=set();configs=set();reviews=[]
for label,packet,nm,nr in tasks:
 P=W/packet;R=J/(label+'-review01');audit=json.loads((R/'audit-result01.json').read_text());imp=json.loads((R/'import-guard-review01.json').read_text());hist=json.loads((R/'source-history-review01.json').read_text());gen=json.loads((R/'source-generation-review01.json').read_text());sem=json.loads((R/'source-semantic-review01.json').read_text());assert audit['declarations']==nr and hist['status']==gen['status']==sem['status']=='PASSED';entries=json.loads((P/'source-object-receipt01.json').read_text());assert len(entries)==nm;mods.extend(entries);all_audits.extend(audit['modules']);roots.update(gen['roots']);configs.update(e['path']for e in imp['execution_configs']);reviews.append(dict(label=label,scope=sem['scope'],modules=nm,reports=nr,original_attempts=hist['attempts'],original_passed=hist['passed'],original_failed=hist['failed']))
 for p in P.rglob('*'):
  if p.is_file():copy(p,Path('producer')/label/p.relative_to(P))
 for p in R.iterdir():
  if p.is_file():copy(p,Path('parent-review')/label/p.name)
assert len(mods)==2 and len({e['module']for e in mods})==2 and sum(len(e['audits'])for e in all_audits)==22
for e in mods:copy(e['source']['path'],Path('source/ShielddSecurity')/(e['module']+'.lean'));copy(e['receipt']['path'],Path('receipts')/Path(e['receipt']['path']).name)
for root in roots:
 for p in Path(root).iterdir():
  if p.is_file():copy(p,Path('maintained-original')/p.relative_to(W),prior=True)
for root in configs:
 root=Path(root);copy(root/'config01.json',Path('maintained-original')/root.relative_to(W)/'config01.json',prior=True);wrapper=json.loads(read(root/'config01.json'))
 if wrapper.get('schema')=='bounded-pinned-execution-delta01':copy(wrapper['base']['path'],Path('maintained-original')/Path(wrapper['base']['path']).relative_to(W),prior=True)
 for p in(root/'maintained').iterdir():copy(p,Path('maintained-original')/p.relative_to(W),prior=True)
P=W/'mac-legal-word-inputs276-278-kernel-result01';R=J/'legal-word-inputs276-278-review01';deps=json.loads((P/'dependencies01.json').read_text());history=json.loads(read(deps['history']['path']));hist=json.loads((R/'source-history-review01.json').read_text())
p=Path(sem['complete_phase_ledger']['path']);copy(p,Path('complete-phase-original')/p.relative_to(W),prior=True)
for e in history['receipts']:
 p=Path(e['path']);copy(p,Path('history-receipts')/(p.parents[2].name+'-'+p.name),prior=True)
for e in hist['rejected']:
 if e['source']is not None:
  p=Path(e['source']['path']);copy(p,Path('rejected-original-source')/p.relative_to(W),prior=True)
copy(deps['history']['path'],Path('maintained-original')/Path(deps['history']['path']).relative_to(W),prior=True);copy(deps['storage_map']['path'],Path('maintained-original')/Path(deps['storage_map']['path']).relative_to(W),prior=True)
for n in ['prepare_legal_word_inputs_publication364.py','review_legal_word_inputs363.py','prepare_source_closure.py','canonical-word215-review01/audit_endpoint.py','review_mac_carried_history_guard28.py','mac-carried-history-cache-guard-review28.json','review_mac_archive_memo_guard26.py','mac-archive-memo-absence-guard-review26.json','mac-raw-history-link-census-guard-review27.json','guard267-archive-reappearance-control01.json','mac-directory-census-guard-review24.json','review_mac_directory_census_guard24.py','mac-metadata-cap-guard-review25.json','mac-metadata-shape-bounds-guard-review23.json','mac-history-shape-alias-equivalence23.json','mac-compact-config-guard-review22.json','mac-inactive-phase-map36-review22.json','review_mac_map36_compact_loader22.py','mac-storage-map29-successor-guard-review21.json','mac-inactive-phase-map31-review20.json','review_mac_resource_preflight_guard18.py','mac-resource-preflight-guard-review18.json','review_mac_phase_identity_guard16.py','mac-phase-identity-guard-review16.json','mac-data-fixture-alias-guard-review17.json','mac-history-cache-source-review14.json','mac-history-cache-deployed-guard-review15.json','read_preserved_mac_config20.py','review_mac_map37_pin115.py','mac-storage-map37-pin-review115.json','review_mac_map38_metadata123.py','mac-storage-map38-review123.json','mac-storage-map38-pin-guard-review135.json','review_mac_map39_metadata154.py','mac-storage-map39-review154.json','mac-storage-map39-pin-guard-review155.json','read_preserved_mac_config15.py']:copy(J/n,Path('parent-review')/n)
for n in ['review_mac_map40_pin200.py','mac-storage-map40-pin-review200.json','review_mac_map41_pin201.py','mac-storage-map41-pin-review201.json','read_preserved_mac_config16.py','read_preserved_mac_config17.py','read_preserved_mac_config18.py','review_mac_metadata43_guard208.py','mac-metadata43-successor-guard-review208.json','review_mac_stdout_preservation204.py','mac-original-stdout-preservation-review204.json','read_preserved_mac_stdout01.py']:
 copy(J/n,Path('parent-review')/n)
for n in ['review_mac_map44_metadata237.py','mac-storage-map44-review237.json']:copy(J/n,Path('parent-review')/n)
for n in ['review_mac_map44_pin251.py','mac-storage-map44-pin-guard-review251.json']:copy(J/n,Path('parent-review')/n)
for n in ['review_mac_alias_preservation299.py','mac-inactive-alias-preservation-review299.json','mac-storage-fixture-identity-review302.json','review_mac_alias_census_hoist307.py','mac-alias-census-hoist-review307.json','review_mac_history_directory_hoist318.py','mac-history-directory-hoist-review318.json','review_mac_official_restoration323.py','mac-official-restoration-review323.json','review_mac_restored_disk_charge324.py','mac-restored-disk-charge-review324.json','review_mac_identity_cardinality332.py','mac-identity-cardinality-review332.json','review_mac_official_union333.py','mac-official-union-review333.json']:
 copy(J/n,Path('parent-review')/n)
for directory in ['mac-inactive-alias-storage275-source02','mac-official-cache277-restoration01','mac-official-cache277-restoration02','mac-official-cache277-restoration03','mac-field-official273-data01']:
 root=W/directory
 for p in root.iterdir():
  if p.is_file()and p.name!='dictionary.bin':copy(p,Path('maintained-original')/p.relative_to(W),prior=True)
# Archived obsolete symlink metadata is formal provenance; no target objects/cache files copied.
for p in (W/'mac-inactive-alias-storage275-source02/archives').glob('*'):
 if p.is_file():copy(p,Path('maintained-original')/p.relative_to(W),prior=True)
for p in (W/'mac-effective-config267-source01').iterdir():
 if p.is_file():copy(p,Path('maintained-original')/p.relative_to(W),prior=True)
for n in [40,41,42,43,44]:
 p=W/('mac-history-metadata-preservation126-'+str(n))/'archive-map01.json';copy(p,Path('maintained-original')/p.relative_to(W),prior=True)
for rawpath,v in json.loads((P/'envelope01.json').read_text())['original_inputs'].items():
 p=Path(rawpath)
 if '/runtime/logs/'in rawpath or '.olean'in p.name:continue
 copy(p,Path('sealed-input-original')/p.relative_to(W),prior=True)
for p in (W/'mac-archive-absence246-source02').iterdir():
 if p.is_file():copy(p,Path('maintained-original/mac-archive-absence246-source02')/p.name)
for p in (W/'mac-carried-proof-cache249-source01').iterdir():
 if p.is_file():copy(p,Path('maintained-original/mac-carried-proof-cache249-source01')/p.name)
(D/'original-byte-map01.json').write_text(json.dumps(dict(kind='Exact originals, large JSON losslessly zlib encoded; no compiled objects/raw logs/caches',files=records),indent=2)+'\n')
(D/'prior-original-byte-references01.json').write_text(json.dumps(dict(files=refs,scope='Exact previously published bytes verified, historical originals retained; no historical or combined kernel replay'),indent=2)+'\n')
files=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
manifest=dict(kind='Constructed three-alias field meanings and exact53-column census;2original modules22reports from phase309;full Transfer OPEN',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',selected_modules={e['module']:dict(path='source/ShielddSecurity/'+e['module']+'.lean',complete_reports=next(len(z['audits'])for z in all_audits if z['module']==e['module']))for e in mods},modules=2,complete_original_reports=22,new_modules=2,new_reports=22,inherited_modules=0,inherited_reports=0,scope=sem['scope'],scoped_original_packets=reviews,files=files,full_transfer='OPEN',combined_replay='UNRUN')
(D/'publication-manifest01.json').write_text(json.dumps(manifest,indent=2)+'\n')
paths=[str(p.relative_to(G))for p in sorted(D.rglob('*'))if p.is_file()];hand=[p for p in paths if p.endswith(('.py','.md','.patch'))or p.endswith('.template.lean')];evidence=[p for p in paths if p not in hand]
for n,ps in [('handwritten',hand),('evidence',evidence)]:(J/('legal-word-inputs276-278-'+n+'-pathspecs.txt')).write_text('\n'.join(ps)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free)
(J/'legal-word-inputs276-278-publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
