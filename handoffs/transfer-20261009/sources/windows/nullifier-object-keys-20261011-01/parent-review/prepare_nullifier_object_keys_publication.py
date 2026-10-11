"""Publish four reviewed source models, original identity maps and precise scope."""
from pathlib import Path
import json,hashlib,shutil
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/windows/nullifier-object-keys-20261011-01';assert not D.exists();assert shutil.disk_usage(W).free>2147483648+8*1024*1024
tasks=[('nullifier-object-keys','windows-nullifier-object-keys-review01','TransferNullifierObjectKeys01',7)]
records=[];omitted=[];selected={}
def sha(b):return hashlib.sha256(b).hexdigest()
def copy(p,n):
 b=p.read_bytes();assert shutil.disk_usage(W).free>2147483648+4*1024*1024+len(b);t=D/n;t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(b);assert t.read_bytes()==b
 records.append(dict(original=dict(path=str(p),bytes=len(b),sha256=sha(b)),publication=dict(path=str(t.relative_to(D)),bytes=len(b),sha256=sha(b))))
for label,name,module,count in tasks:
 R=J/name;P=R/'packet01';review=json.loads((R/'endpoint-audit-review01.json').read_bytes());assert review['fresh_modules']==1 and review['fresh_reports']==count
 for p in sorted(P.rglob('*')):
  if not p.is_file():continue
  if p.name in ['compiler-output.txt','stdout.txt','stderr.txt']:omitted.append(dict(original=dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p.read_bytes())),reason='Raw compiler output excluded; complete qualified reports and structured rejection diagnostics retained'));continue
  copy(p,Path(label)/p.relative_to(P))
 for n in ['endpoint-audit-review01.json','transport-verification01.json','decode_transport.py','preparation-merge-review01.json','ancestor-source-mapping-review01.json','source-regeneration-review01.json']:
  if(R/n).is_file():copy(R/n,Path('parent-review')/label/n)
 selected[module]=dict(path=str(Path(label)/'source/ShielddSecurity'/(module+'.lean')),complete_reports=count)
for n in ['review_cached_windows_endpoint.py','windows-reviewed-ancestry-pool336-reports34-modules01.json','windows-cached-review-pipeline-test01.json','prepare_nullifier_object_keys_publication.py']:copy(J/n,Path('parent-review')/n)
(D/'original-byte-map01.json').write_text(json.dumps(dict(kind='Exact source/receipt/type/runtime/review bytes; no objects/raw logs/caches',files=records,omitted_raw_output=omitted),indent=2)+'\n')
files=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Pinned runtime object-key literals derive retained-pending key separation',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',selected_modules=selected,selected_complete_reports=7,scope='Four generated source-key byte definitions and three generated theorems have7 original complete reports, with336 inherited reports/34owned modules. Exact pinned Rust literals for pending-nullifier, cached SCT, pending-note and pending-volume object keys independently extract/regenerate byte exactly; kernel byte separation and explicit injective representation projection discharge the three prior key inequalities. Whole successful delivery in both contexts/all index modes retains the actual admitted encoded pending vector with ordered append/capacity/non-sealed/per-input freshness. No desired callback/frame/poststate/key inequality/admitted vector premise. Nonempty input/capacity relation and object getter/reader/codec/token/proof/byte projection/ownership/native/Host/durability/fullTransfer remain OPEN. Literal/source hashes give identity only; no cryptographic hash injectivity or native semantic correspondence claim. Exact reviewed ancestry cached with pinned original qualification and review anchors, no new ancestor replay. Physical protections unchanged',files=files,full_transfer='OPEN',native_execution='UNRUN'),indent=2)+'\n')
paths=[str(p.relative_to(G))for p in sorted(D.rglob('*'))if p.is_file()];hand=[p for p in paths if p.endswith(('.py','.md','.rs'))];evidence=[p for p in paths if p not in hand]
a=G/'.gitattributes'
for tree in D.rglob('tree.rs'):
 if any(line.rstrip(b'\r')!=line.rstrip(b'\r').rstrip(b' \t')for line in tree.read_bytes().splitlines()):
  a.write_text(a.read_text()+f'\n{tree.relative_to(G)} whitespace=-blank-at-eof,-blank-at-eol\n')
  if '.gitattributes'not in hand:hand.append('.gitattributes')
for n,v in [('handwritten',hand),('evidence',evidence)]:(J/('nullifier-object-keys-'+n+'-pathspecs.txt')).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free)
(J/'nullifier-object-keys-publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
