"""Publish one reviewed source models, original identity maps and precise scope."""
from pathlib import Path
import json,hashlib,shutil
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/windows/fixed-finalizer-publication-20261011-01';assert not D.exists();assert shutil.disk_usage(W).free>2147483648+8*1024*1024
tasks=[('fixed-finalizer-publication','windows-fixed-finalizer-publication-review01','TransferFixedFinalizerPublication01',8)]
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
 for n in ['endpoint-audit-review01.json','transport-verification01.json','decode_transport.py','preparation-merge-review01.json','ancestor-source-mapping-review01.json','source-regeneration-review01.json','semantic-source-review01.json','semantic-replay-review01.json','utility-source-authentication01.json','unused-runtime-source-review.json','command-carrier-review01.json','recovered-missing-pin-review01.json']:
  if(R/n).is_file():copy(R/n,Path('parent-review')/label/n)
 for p in sorted((R/'original-missing-pin-supplement01').iterdir()):copy(p,Path('parent-review')/label/'original-missing-pin-supplement01'/p.name)
 selected[module]=dict(path=str(Path(label)/'source/ShielddSecurity'/(module+'.lean')),complete_reports=count)
for n in ['review_cached_windows_recovery_ancestry_endpoint01.py','windows-reviewed-ancestry-pool886-reports96-modules01.json','review_cached_windows_scalar_word_primitives_endpoint01.py','review_cached_windows_scalar_carry_schedule_endpoint01.py','review_cached_windows_scalar_four_round_wrapper_endpoint01.py','review_scalar_word_carry_wrapper_semantics01.py','windows-scalar-word-primitives-review01/semantic-replay-review01.json','review_cached_windows_source_typed_input_projection_endpoint01.py','prepare_fixed_finalizer_model_publication01.py']:copy(J/n,Path('parent-review')/n)
(D/'original-byte-map01.json').write_text(json.dumps(dict(kind='Exact source/receipt/type/runtime/review bytes; no objects/raw logs/caches',files=records,omitted_raw_output=omitted),indent=2)+'\n')
files=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Original defined six-key finalizer model with explicit source-order gap',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',selected_modules=selected,selected_complete_reports=8,scope='Original defined six-key finalizer model8 complete reports, independently checked types/standard axioms and96module886report ancestry/exact maintained model generation. Defined order routes deletion before compliance drains; authenticated Rust order drains compliance first. Exact native-order correspondence is OPEN and a fresh corrected worker proof7 has passed reported, pending independent review. These original model theorems are not promoted to exact native order/full native trace. Missing original6767B call-shape plan pin recovered with exact original SHA from a newer original transport, without changing original59file packet or proof replay. Native controls/combined replay/full Transfer OPEN',files=files,full_transfer='OPEN',native_execution='UNRUN'),indent=2)+'\n')
paths=[str(p.relative_to(G))for p in sorted(D.rglob('*'))if p.is_file()];hand=[p for p in paths if p.endswith(('.py','.md','.rs','.lean'))];evidence=[p for p in paths if p not in hand]
a=G/'.gitattributes'
for tree in D.rglob('tree.rs'):
 if any(line.rstrip(b'\r')!=line.rstrip(b'\r').rstrip(b' \t')for line in tree.read_bytes().splitlines()):
  a.write_text(a.read_text()+f'\n{tree.relative_to(G)} whitespace=-blank-at-eof,-blank-at-eol\n')
  if '.gitattributes'not in hand:hand.append('.gitattributes')
for n,v in [('handwritten',hand),('evidence',evidence)]:(J/('fixed-finalizer-publication-'+n+'-pathspecs.txt')).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free)
(J/'fixed-finalizer-publication-publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
