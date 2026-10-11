"""Stage exact reviewed relation/epoch/zero-test joins; retain original identity maps."""
from pathlib import Path
import hashlib,json,zlib,shutil
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/mac/full-relation-epoch-zero64-68';assert not D.exists();assert shutil.disk_usage(W).free>2147483648+48*1024*1024
tasks=[('full-captured-epoch64','mac-full-captured-epoch64-kernel-result01'),('registry-epoch66','mac-registry-epoch-semantic66-kernel-result01'),('global-zero68','mac-global-zero-completion68-kernel-result01')]
records=[];seen={}
def sha(b):return hashlib.sha256(b).hexdigest()
def copy(p,n,compress=False):
 p=Path(p);b=p.read_bytes();original=dict(path=str(p),bytes=len(b),sha256=sha(b))
 if original['sha256']in seen:return seen[original['sha256']]
 t=D/n;t.parent.mkdir(parents=True,exist_ok=True);assert shutil.disk_usage(W).free>2147483648+16*1024*1024
 with t.open('xb')as f:f.write(zlib.compress(b,1)if compress else b)
 check=t.read_bytes();assert(zlib.decompress(check)if compress else check)==b
 r=dict(original=original,publication=dict(path=str(t.relative_to(D)),bytes=len(check),sha256=sha(check)),encoding='zlib'if compress else'identity');records.append(r);seen[original['sha256']]=r;return r
old=G/'handoffs/transfer-20261009/sources/mac/full-arithmetic45-52/original-byte-map01.json';old_pins={e['original']['sha256']:e for e in json.loads(old.read_bytes())['files']}
original_refs=[];source_modules={}
for label,packet in tasks:
 P=W/packet;R=J/(label+'-review01')
 for p in sorted(P.iterdir()):
  if p.is_file():copy(p,Path('producer')/label/p.name)
 mods=json.loads((P/'qualified-modules01.json').read_bytes())
 for e in mods:
  source_modules[e['name']]=e;copy(e['source']['path'],Path('source/ShielddSecurity')/(e['name']+'.lean'));copy(e['receipt']['path'],Path('receipts')/Path(e['receipt']['path']).name)
 for n in ['audit_endpoint.py','audit-result01.json','verify_imports_guards.py','import-guard-review01.json','source-history-review01.json','semantic-body-review01.json','data-review01.json','endpoint-review.md']:
  if(R/n).is_file():copy(R/n,Path('parent-review')/label/n)
 for e in json.loads((P/'maintained-references01.json').read_bytes()):
  p=Path(e['path']);copy(p,Path('maintained-original')/p.relative_to(W),p.name=='config01.json')
 hist=json.loads((P/'attempt-history01.json').read_bytes())
 for e in hist['receipts']:
  if e['sha256']in old_pins:
   original_refs.append(dict(original=e,prior_publication=old_pins[e['sha256']]));continue
  p=Path(e['path']);copy(p,Path('history-receipts')/(p.parent.parent.parent.name+'-'+p.name+'.zlib'),True)
for n in ['review_new_join_sources_history.py','review_join_guards_data.py','join-guard-review01.json','prepare_join_publication.py']:copy(J/n,Path('parent-review')/n)
history_tree=json.loads((J/'join-guard-review01.json').read_bytes())['history_manifests']
current_history=[json.loads((W/packet/'envelope01.json').read_bytes())['historical_provenance']for _,packet in tasks]
for e in current_history:
 if e['sha256']in old_pins:original_refs.append(dict(original=e,prior_publication=old_pins[e['sha256']]));continue
 p=Path(e['path']);copy(p,Path('historical-metadata')/(p.parent.name+'-'+p.name+'.zlib'),True)
assert len(source_modules)==9
for n,v in [('original-byte-map01.json',dict(kind='Lossless publication records; no objects/raw logs/caches',files=records)),('prior-original-byte-references01.json',dict(prior_packet='../full-arithmetic45-52',original_files=original_refs,historical_ancestor_identity_references=history_tree,scope='Only current carried history snapshots are copied; ancestors remain exact reviewed original identity references. This is not a standalone historical-cache transport or final replay.'))]:
 (D/n).write_text(json.dumps(v,indent=2)+'\n')
manifest=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Reviewed actual relation/epoch/zero-test joins only',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',modules=9,complete_original_reports=196,constructed_actual_assertions=75,files=manifest,full_transfer='OPEN'),indent=2)+'\n')
paths=sorted(str(p.relative_to(G))for p in D.rglob('*')if p.is_file());hand=[p for p in paths if p.endswith(('.py','.md'))or '/template.lean'in p];evidence=[p for p in paths if p not in hand]
for n,v in [('pathspecs.txt',paths),('handwritten-pathspecs.txt',hand),('evidence-pathspecs.txt',evidence)]:(J/('join-'+n)).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free)
(J/'join-publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
