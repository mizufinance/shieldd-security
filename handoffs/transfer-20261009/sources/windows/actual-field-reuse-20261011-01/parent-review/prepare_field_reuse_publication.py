"""Publish exact reused field certificate provenance and complete reports, without raw logs."""
from pathlib import Path
import json,hashlib,shutil
J=Path(__file__).parent;W=J.parent;G=W/'shared-build-handoff';R=J/'windows-field-reuse-review01';P=R/'packet01';D=G/'handoffs/transfer-20261009/sources/windows/actual-field-reuse-20261011-01';assert not D.exists();assert shutil.disk_usage(W).free>2147483648+4*1024*1024
review=json.loads((R/'endpoint-audit-review01.json').read_text());assert review['status']=='PASSED'and review['existing_reports']==10 and review['fresh_reports']==0
records=[];omitted=[]
def sha(b):return hashlib.sha256(b).hexdigest()
def copy(p,n):
 b=p.read_bytes();t=D/n;t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(b);assert t.read_bytes()==b;records.append(dict(original=dict(path=str(p),bytes=len(b),sha256=sha(b)),publication=dict(path=str(n),bytes=len(b),sha256=sha(b))))
for p in sorted(P.rglob('*')):
 if not p.is_file():continue
 if p.name in ['memory.txt','start.txt','end.txt','stderr.txt','exit.txt']:
  omitted.append(dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p.read_bytes()),reason='Raw execution logs excluded; original published structured receipt and independent complete report review retained'));continue
 n=Path('reports/reused-field-10-complete-declarations.txt')if p.name=='stdout.txt'else Path('packet')/p.relative_to(P);copy(p,n)
for p in [R/'endpoint-audit-review01.json',R/'transport-verification01.json',R/'decode_transport.py',J/'review_field_reuse_endpoint.py',J/'prepare_field_reuse_publication.py']:copy(p,Path('parent-review')/p.name)
(D/'original-byte-map01.json').write_text(json.dumps(dict(kind='Exact reused original sources/receipts/full declarations; no fresh proof or objects/logs',files=records,omitted_raw_logs=omitted),indent=2)+'\n')
files=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=sha(p.read_bytes()))for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Actual-field certificate reuse and exact constructor parameter identity',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',existing_reports=10,fresh_reports=0,fresh_lean_processes=0,scope=review['application'],native_correspondence='OPEN',full_transfer='OPEN',files=files),indent=2)+'\n')
paths=[str(p.relative_to(G))for p in sorted(D.rglob('*'))if p.is_file()];hand=[p for p in paths if p.endswith(('.py','.md','.lean'))];evidence=[p for p in paths if p not in hand]
for n,v in [('handwritten',hand),('evidence',evidence)]:(J/('field-reuse-'+n+'-pathspecs.txt')).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(paths),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence),free_bytes=shutil.disk_usage(W).free);(J/'field-reuse-publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
