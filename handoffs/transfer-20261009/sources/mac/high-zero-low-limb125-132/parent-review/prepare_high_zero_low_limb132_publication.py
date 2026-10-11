"""Compact exact publication of nine reviewed connected constructor modules."""
from pathlib import Path
import json,hashlib,zlib,shutil,importlib.util
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/mac/high-zero-low-limb125-132';assert not D.exists();assert shutil.disk_usage(W).free>2147483648+4*1024*1024
tasks=[('high-zero125-128','mac-high-zero125-128-kernel-result01'),('low-limb129-132','mac-low-limb129-132-kernel-result01')]
pspec=importlib.util.spec_from_file_location('preserved',J/'read_preserved_mac_config01.py');preserved=importlib.util.module_from_spec(pspec);pspec.loader.exec_module(preserved)
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
for name in ['full-arithmetic45-52','full-relation-epoch-zero64-68','registered-position69-77','subgroup-source78-81','four-subgroups82','subgroup-constructor83-85','four-subgroup-constructor86-89','global-subgroup90-94','regulated-asset95-96','registry-value97-99','comparison100-104','value-canonical105-108','asset-canonical109-113','next-canonical114-118','high-limb119-124']:
 for e in json.loads((G/'handoffs/transfer-20261009/sources/mac'/name/'original-byte-map01.json').read_bytes())['files']:old[e['original']['sha256']]=dict(packet=name,record=e)
modules={}
for label,packet in tasks:
 P=W/packet;R=J/(label+'-review01')
 for p in sorted(P.iterdir()):
  if p.is_file():copy(p,Path('producer')/label/p.name)
 for e in json.loads((P/'qualified-modules01.json').read_bytes()):
  assert e['name']not in modules;modules[e['name']]=e;copy(e['source']['path'],Path('source/ShielddSecurity')/(e['name']+'.lean'));copy(e['receipt']['path'],Path('receipts')/Path(e['receipt']['path']).name)
 for p in R.iterdir():
  if p.is_file()and p.name in ['audit_endpoint.py','audit-result01.json','verify_imports_guards.py','import-guard-review01.json','review_source_data_history.py','source-data-history-review01.json','source-history-review01.json','endpoint-audit-review01.json']:copy(p,Path('parent-review')/label/p.name)
 for e in json.loads((P/'maintained-references01.json').read_bytes()):
  if e['sha256']in old:refs.append(dict(original=e,prior_publication=old[e['sha256']]));continue
  p=Path(e['path']);copy(p,Path('maintained-original')/p.relative_to(W))
 for e in json.loads((P/'attempt-history01.json').read_bytes())['receipts']:
  if e['sha256']in old:refs.append(dict(original=e,prior_publication=old[e['sha256']]));continue
  p=Path(e['path']);copy(p,Path('history-receipts')/(p.parent.parent.parent.name+'-'+p.name))
for n in ['review_high_zero_low_limb132_history.py','review_high_zero_low_data01.py','prepare_high_zero_low_limb132_publication.py','read_preserved_mac_config01.py','review_mac_archived_metadata_guard01.py','mac-archived-metadata-guard-review01.json','pending-mac-archived-metadata-guard-delta01.diff']:copy(J/n,Path('parent-review')/n)
for label in ['high-zero126','low-limb129']:
 copy(J/(label+'-data-review01')/'data-review01.json',Path('parent-review/captured-data')/label/'data-review01.json')
copy(J.parent/'mac-history-metadata-preservation126-10/archive-map01.json',Path('maintained-original/mac-history-metadata-preservation126-10/archive-map01.json'))
assert len(modules)==9
(D/'original-byte-map01.json').write_text(json.dumps(dict(kind='Exact original bytes; large JSON losslessly encoded, no objects/logs/cache/database',files=records),indent=2)+'\n')
unique_refs={}
for ref in refs:
 key=(ref['original']['path'],ref['original']['sha256'])
 if key in unique_refs:assert unique_refs[key]==ref
 unique_refs[key]=ref
(D/'prior-original-byte-references01.json').write_text(json.dumps(dict(files=list(unique_refs.values()),scope='Published predecessors referenced once per exact original identity; original carried metadata remains local. This is not final replay or standalone historical-cache transport.'),indent=2)+'\n')
manifest=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Captured high-zero and low-limb constructors with shared1202assertion join',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',modules=9,complete_original_reports=91,scope='Nine modules91 original complete reports across independently sealed5/53 and4/38 packets. Actual high-zero assertions179023..179025 use independently seeded flag1110/inverse1111 and four actual product rows11032..11035. Generic128 low-bit value/recombination, independent bounded low128 difference/borrow hints1112..1241, exact131 actual low-limb assertions179026..179156. Original1071 construction runs after low hint seeding; SAME final assignment all177954 arithmetic and1202 DISTINCT assertions177954..178116 plus178118..179156. Anchor178117 OPEN, not contiguous1203prefix; remaining21614 assertions/fullTransfer/native OPEN. Original legal RegistrySem/roles/sink/preimage-eight/OnCurve/NoUnitSquare/imaginary premises explicit, no desired comparison/assertion truth or initial satisfaction premise. Original extraction replay and independent readonly SQL verify high-zero515 nodes/260 constants/4 products/3 assertions and low-limb902 nodes/390 constants/131 assertions with exact original certificates and independent signed recipes. All88 failed module attempts in original913-attempt history remain entire failures, with no semantic negative result. Source-only/stopped preparations retained. Historical high-limb prose in low-limb generator metadata is template attribution only; actual Lean contracts/DATA and current scope establish low128/131 rows. Archive-aware guard preserves exact original config pins via immutable map/bounded lossless archives; root independently verified132 original configs375529518 bytes. Physical safeguards/launch/monitor/cleanup unchanged. No fresh ancestor or combined replay',files=manifest,full_transfer='OPEN'),indent=2)+'\n')
paths=[str(p.relative_to(G))for p in sorted(D.rglob('*'))if p.is_file()];hand=[p for p in paths if p.endswith(('.py','.md'))or'/template.lean'in p];evidence=[p for p in paths if p not in hand]
for n,v in [('handwritten',hand),('evidence',evidence)]:(J/('high-zero-low-limb-'+n+'-pathspecs.txt')).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free)
(J/'high-zero-low-limb-publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
