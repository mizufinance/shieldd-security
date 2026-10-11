"""Publish four reviewed source models, original identity maps and precise scope."""
from pathlib import Path
import json,hashlib,shutil
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/windows/captured-recovery-20261011-01';assert not D.exists();assert shutil.disk_usage(W).free>2147483648+8*1024*1024
tasks=[('captured-recovery','windows-captured-recovery-review01','TransferCapturedRecovery01',8)]
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
 for n in ['endpoint-audit-review01.json','transport-verification01.json','decode_transport.py','preparation-merge-review01.json','ancestor-source-mapping-review01.json','source-regeneration-review01.json','semantic-source-review01.json']:
  if(R/n).is_file():copy(R/n,Path('parent-review')/label/n)
 selected[module]=dict(path=str(Path(label)/'source/ShielddSecurity'/(module+'.lean')),complete_reports=count)
for n in ['review_cached_windows_captured_recovery_endpoint01.py','windows-reviewed-ancestry-pool622-reports62-modules01.json','windows-cached-review-pipeline-test01.json','prepare_captured_recovery_publication.py','captured-recovery-rust-source-review01.json']:copy(J/n,Path('parent-review')/n)
(D/'original-byte-map01.json').write_text(json.dumps(dict(kind='Exact source/receipt/type/runtime/review bytes; no objects/raw logs/caches',files=records,omitted_raw_output=omitted),indent=2)+'\n')
files=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Source captured-root recovery agrees with original recurrence under explicit forward partition frames',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',selected_modules=selected,selected_complete_reports=8,scope='Exact source rollback selection uses captured initial actual_roots while physical callback outcomes thread current progress. Symbolic recurrence covers all sixteen partitions without unrolling. Explicit ForwardPartitionFrames callback contract preserves later partition observations after successful earlier rollback and is the necessary native NOMT/locking/observation interface for reusing original changing-root recovery; it never forces own-root restoration, success, healthy state or durability. Eight reports (four program/contract definitions, four proofs) establish recurrence equivalence under frames/tail correspondence, failing callback progress/suffix suppression, source prepare and full recovery equality under explicit native frames. Original recovery reports reused once without replay. Independently observed physical root/poison semantics, actual final root read, native partition representation/session isolation/locks, serde/file IO, ownership and source execution correspondence remain interfaces. Zero native/control/full certification. All eight declarations retain full original type/axiom reports. Whole 01 compiler failure and 03 unused-simp warning earn zero credit; prepared 02 never executed. Only induction/final equality tactics repaired; definitions/contracts and native forward-frame premise unchanged. Rejected object retained unused, no object bytes. Native frames/observations/ownership/IO/library/OS interfaces remain explicit. Zero native/control/full certification credit.',files=files,full_transfer='OPEN',native_execution='UNRUN'),indent=2)+'\n')
paths=[str(p.relative_to(G))for p in sorted(D.rglob('*'))if p.is_file()];hand=[p for p in paths if p.endswith(('.py','.md','.rs','.lean'))];evidence=[p for p in paths if p not in hand]
a=G/'.gitattributes'
for tree in D.rglob('tree.rs'):
 if any(line.rstrip(b'\r')!=line.rstrip(b'\r').rstrip(b' \t')for line in tree.read_bytes().splitlines()):
  a.write_text(a.read_text()+f'\n{tree.relative_to(G)} whitespace=-blank-at-eof,-blank-at-eol\n')
  if '.gitattributes'not in hand:hand.append('.gitattributes')
for n,v in [('handwritten',hand),('evidence',evidence)]:(J/('captured-recovery-'+n+'-pathspecs.txt')).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free)
(J/'captured-recovery-publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
