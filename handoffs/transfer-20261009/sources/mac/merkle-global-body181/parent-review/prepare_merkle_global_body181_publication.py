"""Compact exact publication of seven reviewed registry/anchor soundness and copy transport modules."""
from pathlib import Path
import json,hashlib,zlib,shutil,importlib.util
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/mac/merkle-global-body181';assert not(D/'original-byte-map01.json').exists();assert shutil.disk_usage(W).free>2147483648+4*1024*1024
tasks=[('merkle-global-body181','mac-merkle-global-body181-kernel-result01')]
pspec=importlib.util.spec_from_file_location('preserved',J/'read_preserved_mac_config07.py');preserved=importlib.util.module_from_spec(pspec);pspec.loader.exec_module(preserved)
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
for name in ['full-arithmetic45-52','full-relation-epoch-zero64-68','registered-position69-77','subgroup-source78-81','four-subgroups82','subgroup-constructor83-85','four-subgroup-constructor86-89','global-subgroup90-94','regulated-asset95-96','registry-value97-99','comparison100-104','value-canonical105-108','asset-canonical109-113','next-canonical114-118','high-limb119-124','high-zero-low-limb125-132','next-comparison-registry133-147','comparison-sound148-152','gap-sound153-156','canonical-decode157-159','registry-anchor160-166','call04-global-indexed167-179','prior-global170']:
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
for n in ['review_merkle_global_body181_history01.py','prepare_merkle_global_body181_publication.py','read_preserved_mac_config07.py','review_mac_archived_metadata_guard03.py','mac-archived-metadata-guard-review03.json','pending-mac-archived-metadata-guard-delta03.diff','mac-preserved-metadata-reader-review03.json','mac-preserved-metadata-reader-review04.json','review_mac_archived_metadata_successors04.py','mac-archived-metadata-successors-review04.json','pending-mac-archived-metadata-guard-delta184.diff','pending-mac-archived-metadata-guard-delta186.diff','review_mac_archived_metadata_successors05.py','mac-archived-metadata-successors-review05.json','pending-mac-archived-metadata-guard-delta187.diff','pending-mac-archived-metadata-guard-delta188.diff','pending-mac-archived-metadata-guard-delta190.diff','pending-mac-archived-metadata-guard-delta195.diff','review_mac_guard_metadata_cache06.py','mac-metadata-cache-guard-review06.json','pending-mac-metadata-cache-guard-delta198.diff','pending-mac-metadata-cache-guard-delta199.diff','mac-preserved-metadata-reader-review07.json','mac-archive-map18-guard-review07.json','pending-mac-archive-map18-guard-delta202.diff']:copy(J/n,Path('parent-review')/n)
for label in []:
 copy(J/(label+'-data-review01')/'data-review01.json',Path('parent-review/captured-data')/label/'data-review01.json')
copy(J.parent/'mac-history-metadata-preservation126-11/archive-map01.json',Path('maintained-original/mac-history-metadata-preservation126-11/archive-map01.json'))
copy(J.parent/'mac-history-metadata-preservation126-12/archive-map01.json',Path('maintained-original/mac-history-metadata-preservation126-12/archive-map01.json'))
copy(J.parent/'mac-history-metadata-preservation126-13/archive-map01.json',Path('maintained-original/mac-history-metadata-preservation126-13/archive-map01.json'))
for number in [14,15,16,17,18]:copy(W/f'mac-history-metadata-preservation126-{number}/archive-map01.json',Path(f'maintained-original/mac-history-metadata-preservation126-{number}/archive-map01.json'))
assert len(modules)==1
(D/'original-byte-map01.json').write_text(json.dumps(dict(kind='Exact original bytes; large JSON losslessly encoded, no objects/logs/cache/database',files=records),indent=2)+'\n')
unique_refs={}
for ref in refs:
 key=(ref['original']['path'],ref['original']['sha256'])
 if key in unique_refs:assert unique_refs[key]==ref
 unique_refs[key]=ref
(D/'prior-original-byte-references01.json').write_text(json.dumps(dict(files=list(unique_refs.values()),scope='Published predecessors referenced once per exact original identity; original carried metadata remains local. This is not final replay or standalone historical-cache transport.'),indent=2)+'\n')
manifest=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Conditional generic Merkle body projection and composition',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',modules=1,complete_original_reports=12,scope='Transparent field-independent bodyRows exactly equals qualified MerkleFamily32Whole.rows for each Fin15 instance; Arithmetic and copy take/drop partitions recompose the exact same body using symbolic membership proof; Copy satisfaction derives from full captured200770 relation ONLY under explicit finite copyCheck true; checking uses replicated actual last captured row200769 plus derived verifier copy links; Final sound theorem retains explicit arithmeticRows satisfaction and copyCheck premises; no final captured global-path claim or desired hash inferred; All12public declarations have complete original reports; exact isolated generation/public census/history1024 verified;112failed original attempts stay failed; Finite per-instance copyCheck and actual arithmetic indexed full captured certificates; Full global Merkle/hash/path/public64/blinding soundness and legal all-row construction; Native correspondence/fullTransfer/final bounded replay',files=manifest,full_transfer='OPEN'),indent=2)+'\n')
paths=[str(p.relative_to(G))for p in sorted(D.rglob('*'))if p.is_file()];hand=[p for p in paths if p.endswith(('.py','.md'))or'/template.lean'in p];evidence=[p for p in paths if p not in hand]
a=G/'.gitattributes';entry=str(D.relative_to(G)/'parent-review/pending-mac-archived-metadata-guard-delta03.diff')+' whitespace=-blank-at-eof,-blank-at-eol';a.write_text(a.read_text()+'\n'+entry+'\n');hand.append('.gitattributes')
for number in [184,186,187,188,190,195,198,199]:
 entry=str(D.relative_to(G)/(f'parent-review/pending-mac-metadata-cache-guard-delta{number}.diff' if number in [198,199] else f'parent-review/pending-mac-archived-metadata-guard-delta{number}.diff'))+' whitespace=-blank-at-eof,-blank-at-eol';a.write_text(a.read_text()+'\n'+entry+'\n')
entry=str(D.relative_to(G)/'parent-review/pending-mac-archive-map18-guard-delta202.diff')+' whitespace=-blank-at-eof,-blank-at-eol';a.write_text(a.read_text()+'\n'+entry+'\n')
for n,v in [('handwritten',hand),('evidence',evidence)]:(J/('merkle-global-body181-'+n+'-pathspecs.txt')).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free)
(J/'merkle-global-body181-publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
