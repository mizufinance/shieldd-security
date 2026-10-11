"""Publish exact row-slice helper and reviewed immutable evidence."""
from pathlib import Path
import json,hashlib,shutil
J=Path(__file__).parent;W=J.parent.parent;G=W/'shared-build-handoff';P=W/'mac-indexed-row-slice63-kernel-result01';D=G/'handoffs/transfer-20261009/sources/mac/indexed-row-slice63'
assert not D.exists();D.mkdir(parents=True)
def copy(p,n):
 p=Path(p);t=D/n;t.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,t);assert p.read_bytes()==t.read_bytes()
mods=json.loads((P/'qualified-modules01.json').read_bytes())
for m in mods:
 copy(m['source']['path'],Path('sources/ShielddSecurity')/(m['module']+'.lean'));copy(m['receipt']['path'],Path('receipts')/(m['module']+'.json'))
for p in P.iterdir():
 if p.is_file():copy(p,Path('producer-result')/p.name)
for p in(W/'mac-indexed-row-slice63-source01').iterdir():
 if p.is_file():copy(p,Path('maintained/mac-indexed-row-slice63-source01')/p.name)
for root in sorted({Path(m['receipt']['path']).parents[2]for m in mods}):
 for n in ['config01.json','overlay-manifest01.json','maintained-inventory01.json','maintained/guard.py','maintained/prepare.py']:copy(root/n,Path('execution-context')/root.name/n)
for n in ['audit_endpoint.py','audit-result01.json','verify_imports_guards.py','import-guard-review01.json','verify_source.py','source-review01.json','endpoint-review.md','prepare_publication.py']:copy(J/n,Path('parent-review')/n)
(D/'README.md').write_text('Reviewed exact indexed row-slice helper: one qualified module/eight complete reports for runtime844389ee069e1fb2e576708842d0b389b4d9a44a. See parent-review/endpoint-review.md. Actual captured-instance checks and full Transfer remain separate. Raw logs/objects/caches/workspaces are excluded; original identities and structured full reports remain intact. No certification.\n')
records=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Reviewed indexed row-slice source/evidence',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',files=records,full_transfer='OPEN'),indent=2)+'\n')
files=sorted(str(p.relative_to(G))for p in D.rglob('*')if p.is_file());hand=[n for n in files if n.endswith(('.py','.md'))];evidence=[n for n in files if n not in hand]
for n,v in [('pathspecs.txt',files),('handwritten-pathspecs.txt',hand),('evidence-pathspecs.txt',evidence)]: (J/n).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(files),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence));(J/'publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
