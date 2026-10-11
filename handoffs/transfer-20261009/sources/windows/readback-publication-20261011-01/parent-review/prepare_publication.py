"""Publish exact maintained state models and structured reviewed evidence."""
from pathlib import Path
import hashlib,json,shutil
J=Path(__file__).parent;P=J/'packet01';G=J.parent.parent/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/windows/readback-publication-20261011-01'
assert not D.exists();D.mkdir(parents=True)
def copy(p,n):
 p=Path(p);t=D/n;t.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,t);assert p.read_bytes()==t.read_bytes()
for p in sorted(P.rglob('*')):
 if p.is_file()and 'reports' not in p.relative_to(P).parts:copy(p,p.relative_to(P))
for n in ['decode_transport.py','transport-verification01.json','verify_endpoint.py','endpoint-audit-review01.json','endpoint-review.md','prepare_publication.py']:copy(J/n,Path('parent-review')/n)
(D/'README.md').write_text('Reviewed fresh replay of three existing symbolic state models/35 complete theorem reports for runtime844389ee069e1fb2e576708842d0b389b4d9a44a. See parent-review/endpoint-review.md. Full types and original compiler output identities are in structured parent review; raw output/object/cache/toolchain bytes are excluded. The external core floor references the exact accepted deferred-queue packet. Concrete Rust/durability refinement and full Transfer certification remain OPEN.\n')
records=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='Reviewed exact existing readback/recovery/publication model replay',runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',files=records,full_transfer='OPEN'),indent=2)+'\n')
files=sorted(str(p.relative_to(G))for p in D.rglob('*')if p.is_file());hand=[n for n in files if n.endswith(('.py','.md','.lean'))];evidence=[n for n in files if n not in hand]
for n,v in [('pathspecs.txt',files),('handwritten-pathspecs.txt',hand),('evidence-pathspecs.txt',evidence)]: (J/n).write_text('\n'.join(v)+'\n')
out=dict(path=str(D),files=len(files),bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),handwritten=len(hand),evidence=len(evidence));(J/'publication-payload01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
