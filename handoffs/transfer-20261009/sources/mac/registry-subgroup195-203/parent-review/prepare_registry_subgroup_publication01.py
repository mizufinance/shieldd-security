"""Compact exact publication of seven reviewed registry/anchor soundness and copy transport modules."""
from pathlib import Path
import json,hashlib,zlib,shutil,importlib.util
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/mac/registry-subgroup195-203';assert not(D/'original-byte-map01.json').exists();assert shutil.disk_usage(W).free>2147483648+4*1024*1024
tasks=[('registry-subgroup195-203','mac-registry-subgroup195-203-kernel-result01')]
pspec=importlib.util.spec_from_file_location('preserved',J/'read_preserved_mac_config10.py');preserved=importlib.util.module_from_spec(pspec);pspec.loader.exec_module(preserved)
records=[];seen={};refs=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def copy(p,n):
 p=Path(p);b=p.read_bytes()if p.exists()else preserved.read_config(p);original=dict(path=str(p),bytes=len(b),sha256=sha(b))
 if original['sha256']in seen:return seen[original['sha256']]
 compressed=p.suffix=='.json'and len(b)>256*1024;encoded=zlib.compress(b,1)if compressed else b
 if compressed:n=Path(str(n)+'.zlib')
 assert shutil.disk_usage(W).free>2147483648+2*1024*1024+len(encoded)
 t=D/n;t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(encoded);assert(zlib.decompress(t.read_bytes())if compressed else t.read_bytes())==b
 r=dict(original=original,publication=dict(path=str(t.relative_to(D)),bytes=len(encoded),sha256=sha(encoded)),encoding='zlib'if compressed else'identity');records.append(r);seen[original['sha256']]=r;return r
old={}
for name in ['full-arithmetic45-52','full-relation-epoch-zero64-68','registered-position69-77','subgroup-source78-81','four-subgroups82','subgroup-constructor83-85','four-subgroup-constructor86-89','global-subgroup90-94','regulated-asset95-96','registry-value97-99','comparison100-104','value-canonical105-108','asset-canonical109-113','next-canonical114-118','high-limb119-124','high-zero-low-limb125-132','next-comparison-registry133-147','comparison-sound148-152','gap-sound153-156','canonical-decode157-159','registry-anchor160-166','call04-global-indexed167-179','prior-global170','merkle-global-body181','natural-registry-merkle-bits188-194']:
 for e in json.loads((G/'handoffs/transfer-20261009/sources/mac'/name/'original-byte-map01.json').read_bytes())['files']:old[e['original']['sha256']]=dict(packet=name,record=e)
modules={}
for label,packet in tasks:
 P=W/packet;R=J/(label+'-review01')
 for p in sorted(P.iterdir()):
  if p.is_file():copy(p,Path('producer')/label/p.name)
 for e in json.loads((P/'qualified-modules01.json').read_bytes()):
  assert e['name']not in modules;modules[e['name']]=e;copy(e['source']['path'],Path('source/ShielddSecurity')/(e['name']+'.lean'));copy(e['receipt']['path'],Path('receipts')/Path(e['receipt']['path']).name)
 for p in R.iterdir():
  if p.is_file()and p.name in ['audit_endpoint.py','audit-result01.json','verify_imports_guards.py','import-guard-review01.json','review_source_data_history.py','source-data-history-review01.json','source-history-review01.json','endpoint-audit-review01.json','semantic-source-review01.json']:copy(p,Path('parent-review')/label/p.name)
 for e in json.loads((P/'maintained-references01.json').read_bytes()):
  if e['sha256']in old:refs.append(dict(original=e,prior_publication=old[e['sha256']]));continue
  p=Path(e['path']);copy(p,Path('maintained-original')/p.relative_to(W))
 for e in json.loads((P/'attempt-history01.json').read_bytes())['receipts']:
  if e['sha256']in old:refs.append(dict(original=e,prior_publication=old[e['sha256']]));continue
  p=Path(e['path']);copy(p,Path('history-receipts')/(p.parent.parent.parent.name+'-'+p.name))
for n in ['review_registry_subgroup_history13.py','prepare_registry_subgroup_publication01.py','review_mac_header_cache10.py','mac-header-cache-guard-review10.json','mac-header-cache-delta209.diff','review_mac_phase_metadata_archive12.py','mac-phase-metadata-guard-review12.json','mac-phase-metadata-delta216.diff','read_preserved_mac_config10.py','read_preserved_mac_config09.py','mac-group-windows-source-body-comparison11.json','mac-recovery-group-source-pre-review11.json']:copy(J/n,Path('parent-review')/n)
for label in []:
 copy(J/(label+'-data-review01')/'data-review01.json',Path('parent-review/captured-data')/label/'data-review01.json')
copy(J.parent/'mac-history-metadata-preservation126-11/archive-map01.json',Path('maintained-original/mac-history-metadata-preservation126-11/archive-map01.json'))
copy(J.parent/'mac-history-metadata-preservation126-12/archive-map01.json',Path('maintained-original/mac-history-metadata-preservation126-12/archive-map01.json'))
copy(J.parent/'mac-history-metadata-preservation126-13/archive-map01.json',Path('maintained-original/mac-history-metadata-preservation126-13/archive-map01.json'))
for number in [19,20,21,22,23,25,27,28]:copy(W/f'mac-history-metadata-preservation126-{number}/archive-map01.json',Path(f'maintained-original/mac-history-metadata-preservation126-{number}/archive-map01.json'))
assert len(modules)==7
(D/'original-byte-map01.json').write_text(json.dumps(dict(kind='Exact original bytes; large JSON losslessly encoded, no objects/logs/cache/database',files=records),indent=2)+'\n')
unique_refs={}
for ref in refs:
 key=(ref['original']['path'],ref['original']['sha256'])
 if key in unique_refs:assert unique_refs[key]==ref
 unique_refs[key]=ref
(D/'prior-original-byte-references01.json').write_text(json.dumps(dict(files=list(unique_refs.values()),scope='Published predecessors referenced once per exact original identity; original carried metadata remains local. This is not final replay or standalone historical-cache transport.'),indent=2)+'\n')
manifest=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Canonical recovery, chosen represented subgroup, Registry conditions and constructive partial subgroup seed',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',modules=7,complete_original_reports=46,scope='Seven original modules46complete named type/axiom reports. Exact isolated maintained generation,1210custom load/source/object/receipt associations and all1141original attempts reviewed;1018passed123failed, with every failure/source/log retained and no reattribution. Full captured satisfaction derives four recovered Registry valid points under explicit CanonicalRepresentation, chosen StandardCurveModel/nonsquare/imaginary/universal8rorder. Epoch/range/regulation/order conditions derive independently. Actual inverse8 constructs preimages from lawful represented scalar-annihilated membership; partial constructor yields all177954arithmetic and four original subgroup row families on one assignment with exact20hint frame. Concrete instances/full hash/path/RegistrySem/all assertion/compatible full seed/native refinements remain OPEN. GroupWindows math bodies match chosen prior published Windows source; wrappers supply full15named audits. Inactive phase metadata archived losslessly with exact pins and unchanged safety/refusal/history/audits. Full Transfer OPEN; native controls and final combined replay UNRUN.',files=manifest,full_transfer='OPEN'),indent=2)+'\n')
paths=[str(p.relative_to(G))for p in sorted(D.rglob('*'))if p.is_file()];hand=[p for p in paths if p.endswith(('.py','.md'))or'/template.lean'in p or p.endswith('/templates01.json')];evidence=[p for p in paths if p not in hand]
a=G/'.gitattributes'
for diff in D.rglob('*.diff'):
 entry=str(diff.relative_to(G))+' whitespace=-blank-at-eof,-blank-at-eol'
 if entry not in a.read_text():
  a.write_text(a.read_text()+'\n'+entry+'\n')
  if '.gitattributes'not in hand:hand.append('.gitattributes')
for n,v in [('handwritten',hand),('evidence',evidence)]:(J/('registry-subgroup195-203-'+n+'-pathspecs.txt')).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free)
(J/'registry-subgroup195-203-publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
