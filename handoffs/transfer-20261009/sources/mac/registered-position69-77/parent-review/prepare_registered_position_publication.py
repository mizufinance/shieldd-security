"""Compact exact publication of nine reviewed connected constructor modules."""
from pathlib import Path
import json,hashlib,zlib,shutil
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/mac/registered-position69-77';assert not D.exists();assert shutil.disk_usage(W).free>2147483648+4*1024*1024
tasks=[('registered-audit71','mac-registered-audit71-kernel-result01'),('global-registered75','mac-global-registered75-kernel-result01'),('regulated-boolean76','mac-regulated-boolean76-kernel-result01'),('global-position77','mac-global-position77-kernel-result01')]
records=[];seen={};refs=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def copy(p,n):
 p=Path(p);b=p.read_bytes();original=dict(path=str(p),bytes=len(b),sha256=sha(b))
 if original['sha256']in seen:return seen[original['sha256']]
 compressed=p.suffix=='.json'and len(b)>256*1024;encoded=zlib.compress(b,1)if compressed else b
 if compressed:n=Path(str(n)+'.zlib')
 assert shutil.disk_usage(W).free>2147483648+2*1024*1024+len(encoded)
 t=D/n;t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(encoded);assert(zlib.decompress(t.read_bytes())if compressed else t.read_bytes())==b
 r=dict(original=original,publication=dict(path=str(t.relative_to(D)),bytes=len(encoded),sha256=sha(encoded)),encoding='zlib'if compressed else'identity');records.append(r);seen[original['sha256']]=r;return r
old={}
for name in ['full-arithmetic45-52','full-relation-epoch-zero64-68']:
 for e in json.loads((G/'handoffs/transfer-20261009/sources/mac'/name/'original-byte-map01.json').read_bytes())['files']:old[e['original']['sha256']]=dict(packet=name,record=e)
modules={}
for label,packet in tasks:
 P=W/packet;R=J/(label+'-review01')
 for p in sorted(P.iterdir()):
  if p.is_file():copy(p,Path('producer')/label/p.name)
 for e in json.loads((P/'qualified-modules01.json').read_bytes()):
  assert e['name']not in modules;modules[e['name']]=e;copy(e['source']['path'],Path('source/ShielddSecurity')/(e['name']+'.lean'));copy(e['receipt']['path'],Path('receipts')/Path(e['receipt']['path']).name)
 for p in R.iterdir():
  if p.is_file()and p.name in ['audit_endpoint.py','audit-result01.json','verify_imports_guards.py','import-guard-review01.json','review_source_data_history.py','source-data-history-review01.json','source-history-review01.json']:copy(p,Path('parent-review')/label/p.name)
 for e in json.loads((P/'maintained-references01.json').read_bytes()):
  if e['sha256']in old:refs.append(dict(original=e,prior_publication=old[e['sha256']]));continue
  p=Path(e['path']);copy(p,Path('maintained-original')/p.relative_to(W))
 for e in json.loads((P/'attempt-history01.json').read_bytes())['receipts']:
  if e['sha256']in old:refs.append(dict(original=e,prior_publication=old[e['sha256']]));continue
  p=Path(e['path']);copy(p,Path('history-receipts')/(p.parent.parent.parent.name+'-'+p.name))
for n in ['review_registered_position_sources_history.py','prepare_registered_position_publication.py']:copy(J/n,Path('parent-review')/n)
assert len(modules)==9
(D/'original-byte-map01.json').write_text(json.dumps(dict(kind='Exact original bytes; large JSON losslessly encoded, no objects/logs/cache/database',files=records),indent=2)+'\n')
unique_refs={}
for ref in refs:
 key=(ref['original']['path'],ref['original']['sha256'])
 if key in unique_refs:assert unique_refs[key]==ref
 unique_refs[key]=ref
(D/'prior-original-byte-references01.json').write_text(json.dumps(dict(files=list(unique_refs.values()),scope='Published predecessors referenced once per exact original identity; original carried metadata remains local. This is not final replay or standalone historical-cache transport.'),indent=2)+'\n')
manifest=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Connected coordinate exclusion/Boolean/position constructor endpoints',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',modules=9,complete_original_reports=88,constructed_actual_assertions=139,scope='All177954 arithmetic rows and139 actual assertions under RegistrySem, exact sink interpretation and original role/constant bindings. Hints changed; only explicit outside frame preserved. Full Transfer/native/portable final replay remain OPEN.',files=manifest,full_transfer='OPEN'),indent=2)+'\n')
paths=[str(p.relative_to(G))for p in sorted(D.rglob('*'))if p.is_file()];hand=[p for p in paths if p.endswith(('.py','.md'))or'/template.lean'in p];evidence=[p for p in paths if p not in hand]
for n,v in [('handwritten',hand),('evidence',evidence)]:(J/('registered-position-'+n+'-pathspecs.txt')).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free)
(J/'registered-position-publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
