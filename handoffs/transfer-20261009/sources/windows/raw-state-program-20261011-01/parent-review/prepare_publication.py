"""Publish maintained raw-state model and reviewed structured evidence."""
from pathlib import Path
import hashlib,json,shutil
J=Path(__file__).parent;P=J/'packet01';G=J.parent.parent/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/windows/raw-state-program-20261011-01'
assert not D.exists();D.mkdir(parents=True)
def write(n,b):
 t=D/n;t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(b)
def copy(p,n):
 b=p.read_bytes();write(n,b);assert(D/n).read_bytes()==b
for p in sorted(P.rglob('*')):
 if not p.is_file():continue
 n=p.relative_to(P)
 if 'reports'in n.parts or p.name=='compiler-output.txt' or n.as_posix()=='rejected/source.lean':continue
 copy(p,n)
for n in ['source.lean','compiler-output.txt']:
 p=P/'rejected'/n;b=p.read_bytes();write(Path('rejected')/(n+'.json'),(json.dumps(dict(kind='Lossless original rejected predecessor bytes; no successful control',bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),utf8=b.decode()),indent=2)+'\n').encode())
a=json.loads((J/'endpoint-audit-review01.json').read_bytes())
for name,key in [('fresh-16','full_declarations'),('inherited-12','inherited_declarations')]:
 write(Path('proof-audits')/(name+'.json'),(json.dumps(dict(kind='Structured complete original output, parent verified original hash',audits=a[key]),indent=2)+'\n').encode())
for n in ['decode_transport.py','transport-verification01.json','verify_endpoint.py','endpoint-audit-review01.json','endpoint-review.md','prepare_publication.py']:copy(J/n,Path('parent-review')/n)
write(Path('README.md'),b'Reviewed failure-aware raw child-cache sequence and delivery adapter: one fresh module/sixteen declarations plus twelve exact retained declarations. No raw rollback claim. Native delayed-token and genuine Host fault controls UNRUN; Rust aliasing/storage/refinement, durability and full Transfer OPEN. See parent-review/endpoint-review.md.\n')
records=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in sorted(D.rglob('*'))if p.is_file()]
write(Path('publication-manifest01.json'),(json.dumps(dict(kind='Reviewed scoped failure-aware raw child cache and delivery composition',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',files=records,full_transfer='OPEN'),indent=2)+'\n').encode())
files=sorted(str(p.relative_to(G))for p in D.rglob('*')if p.is_file());hand=[n for n in files if n.endswith(('.py','.md','.lean','.rs'))];evidence=[n for n in files if n not in hand]
for n,v in [('pathspecs.txt',files),('handwritten-pathspecs.txt',hand),('evidence-pathspecs.txt',evidence)]:(J/n).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(files),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence));(J/'publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
