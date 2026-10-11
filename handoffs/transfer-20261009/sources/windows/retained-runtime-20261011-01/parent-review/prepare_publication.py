"""Publish reviewed retained-result identities and source boundaries, excluding raw logs."""
from pathlib import Path
import hashlib,json,shutil
J=Path(__file__).resolve().parent;P=J/'packet01';G=J.parent.parent/'shared-build-handoff'
D=G/'handoffs/transfer-20261009/sources/windows/retained-runtime-20261011-01';D.mkdir(parents=True,exist_ok=False)
def copy(source,relative):
 dest=D/relative;dest.parent.mkdir(parents=True,exist_ok=True);assert source.suffix not in ['.stdout','.stderr','.olean']
 shutil.copyfile(source,dest)
for name in ['assembly-recipe.py','manifest.json','completion-status02.json','source-boundary-review.json',
 'receipt-review/review.json','receipt-review/review.py','overlay-review/capture.json','overlay-review/capture.py']:
 copy(P/name,Path(name))
for p in sorted((P/'overlay-review/diffs').rglob('*')):
 if p.is_file():
  raw=p.read_bytes();relative=p.relative_to(P);target=D/Path(str(relative)+'.json');target.parent.mkdir(parents=True,exist_ok=True)
  target.write_text(json.dumps(dict(kind='EXACT_UTF8_DIFF_BYTES',original_path=relative.as_posix(),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),content_utf8=raw.decode()),indent=2)+'\n')
for p in sorted((P/'retained-receipts').rglob('*.json')):
 if p.name in ['runtime-completed.json','binary-before.json','build-receipt.json','group-result.json','alternate-registry-published.json','source-stage-validated.json']:
  copy(p,p.relative_to(P))
for p in sorted((P/'retained-execution-source').glob('*/manifest.json')):copy(p,p.relative_to(P))
for n in ['verify_retained_runtime.py','independent-receipt-review01.json','reconstruct_overlay.py',
 'source-diff-reconstruction01.json','source-diff-reconstruction02.json','endpoint-review.md','prepare_publication.py','transport-verification01.json']:
 copy(J/n,Path('parent-review')/n)
S=J.parent/'windows-runtime-overlay-supplement-review01/packet01'
for p in sorted(S.rglob('*')):
 if p.is_file():copy(p,Path('overlay-byte-supplement')/p.relative_to(S))
(D/'README.md').write_text('Independently reviewed retained finite native Transfer evidence:23 named tests and17 genuine branch proofs; exact runtime844389ee069e1fb2e576708842d0b389b4d9a44a diagnostic overlay. See parent-review/endpoint-review.md. Original manifest entries are retained source/receipt identity references, including omitted raw logs. Exact original diffs are reversibly encoded as JSON content_utf8 with byte count and SHA256; no diff bytes were normalized. No certification,universal native refinement,new test replay,executables,keys,caches or composed workspaces.\n')
records=[dict(path=p.relative_to(D).as_posix(),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='RETAINED_FINITE_NATIVE_RESULTS_AND_SOURCE_BOUNDARIES',files=records,full_transfer='OPEN',certification=False,new_runtime_executions=0,raw_logs_included=False),indent=2)+'\n')
hand=[];evidence=[]
for p in sorted(D.rglob('*')):
 if p.is_file():(hand if p.suffix in ['.py','.md','.diff'] else evidence).append(p.relative_to(G).as_posix())
for name,values in [('handwritten',hand),('generated',evidence)]:(J/(name+'-pathspec01.nul')).write_bytes(b'\0'.join(n.encode()for n in values)+b'\0')
result=dict(path=str(D),files=len(records)+1,bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence))
(J/'publication-payload01.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))

