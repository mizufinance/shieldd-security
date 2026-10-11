"""Stage reviewed exact Windows packet bytes, with explicit successor scope."""
from pathlib import Path
import hashlib,json,shutil
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/windows/nullifier-and-raw-effects-20261011-01';assert not D.exists()
assert shutil.disk_usage(W).free>2147483648+4*1024*1024
records=[];omitted=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def copy(p,target):
 b=p.read_bytes();assert shutil.disk_usage(W).free>2147483648+2*1024*1024+len(b)
 t=D/target;t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(b);assert t.read_bytes()==b
 records.append(dict(original=dict(path=str(p),bytes=len(b),sha256=sha(b)),publication=dict(path=str(t.relative_to(D)),bytes=len(b),sha256=sha(b))))
for label,name in [('batch','windows-nullifier-batch-review01'),('raw-predecessor','windows-raw-effects-review01'),('fee-funding-successor','windows-raw-effects-fee-correction-review01')]:
 R=J/name;P=R/'packet01';assert(R/'endpoint-audit-review01.json').is_file()
 for p in sorted(P.rglob('*')):
  if not p.is_file():continue
  if p.name=='compiler-output.txt':omitted.append(dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p.read_bytes()),reason='Raw rejected compiler log excluded; structured diagnostics and exact source delta retained in parent review'));continue
  copy(p,Path(label)/p.relative_to(P))
 for n in ['verify_endpoint.py','endpoint-audit-review01.json','transport-verification01.json']:copy(R/n,Path('parent-review')/label/n)
copy(Path(__file__),Path('parent-review')/Path(__file__).name)
(D/'original-byte-map01.json').write_text(json.dumps(dict(kind='Exact source/receipt/report/runtime packet publication; original transported metadata retained, no objects or raw logs',files=records,omitted_raw_logs=omitted),indent=2)+'\n')
files=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Two selected modeled source modules; successor names match exact runtime FeeFunding context',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',selected_modules={'TransferNullifierBatchSource01':'batch/source/ShielddSecurity/TransferNullifierBatchSource01.lean','TransferRawEffectsSource01':'fee-funding-successor/source/ShielddSecurity/TransferRawEffectsSource01.lean'},selected_complete_reports=43,inherited_complete_reports=57,predecessor_scope='23-report and 27-report raw predecessors retained as original context; no additional selected-module count or combined replay',files=files,full_transfer='OPEN',native_execution='UNRUN'),indent=2)+'\n')
paths=[str(p.relative_to(G))for p in sorted(D.rglob('*'))if p.is_file()];hand=[p for p in paths if p.endswith(('.py','.md','.rs','.lean'))];evidence=[p for p in paths if p not in hand]
for n,v in [('handwritten',hand),('evidence',evidence)]:(J/('batch-raw-'+n+'-pathspecs.txt')).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free)
(J/'batch-raw-publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
