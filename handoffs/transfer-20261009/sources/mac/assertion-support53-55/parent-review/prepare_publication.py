from pathlib import Path
import hashlib,json,shutil
V=Path(__file__).resolve().parent;W=V.parent.parent;G=W/'shared-build-handoff';P=W/'mac-assertion-support53-55-kernel-result01'
D=G/'handoffs/transfer-20261009/sources/mac/assertion-support53-55';D.mkdir(parents=True,exist_ok=False)
def copy(p,name):
 target=D/name;target.parent.mkdir(parents=True,exist_ok=True)
 assert not p.name.endswith(('.olean','.stdout','.stderr'))
 if target.exists():assert target.read_bytes()==p.read_bytes()
 else:shutil.copyfile(p,target)
for p in P.glob('*.json'):copy(p,Path('provenance')/p.name)
copy(P/'seal.py',Path('maintained')/P.name/'seal.py')
for e in json.loads((P/'qualified-modules01.json').read_bytes()):
 copy(Path(e['source']['path']),Path('sources/ShielddSecurity')/(e['module']+'.lean'))
 copy(Path(e['receipt']['path']),Path('receipts/accepted')/Path(e['receipt']['path']).name)
for x in json.loads((P/'maintained-references01.json').read_bytes()):
 p=Path(x['path']);b=p.read_bytes();assert len(b)==x['bytes'] and hashlib.sha256(b).hexdigest()==x['sha256']
 copy(p,Path('maintained')/p.relative_to(W))
for e in json.loads((P/'failures01.json').read_bytes()):
 for key in ['source','receipt']:
  p=Path(e[key]['path']);copy(p,Path('provenance/history')/p.relative_to(W))
for name in ['audit-result01.json','verify_imports_guards.py','import-guard-review02.json','verify_generation_guard.py','generation-guard-review01.json','guard-delta01.diff','endpoint-review.md']:
 copy(V/name,Path('parent-review')/name)
copy(V.parent/'assertion-block51-review01/audit_endpoint.py',Path('parent-review/audit_endpoint.py'))
copy(Path(__file__),Path('parent-review/prepare_publication.py'))
(D/'README.md').write_text('Reviewed generic assertion-pair and verifier-link proof sources and evidence. Runtime844389ee069e1fb2e576708842d0b389b4d9a44a; see parent-review/endpoint-review.md. Full Transfer remains OPEN. Compiler objects, raw logs, caches, toolchains, and composed workspaces are excluded.\n')
files=[dict(path=p.relative_to(D).as_posix(),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(D.rglob('*')) if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='SCOPED_SOURCE_AND_EVIDENCE',files=files,full_transfer='OPEN'),indent=2)+'\n')
prefix=D.relative_to(G)
hand=[];generated=[]
for p in sorted(D.rglob('*')):
 if not p.is_file():continue
 dest=hand if p.suffix in ['.py','.md','.diff'] or (p.name=='template.lean') else generated
 dest.append((prefix/p.relative_to(D)).as_posix())
(V/'handwritten-pathspec01.nul').write_bytes(b'\0'.join(x.encode() for x in hand)+b'\0')
(V/'generated-pathspec01.nul').write_bytes(b'\0'.join(x.encode() for x in generated)+b'\0')
(V/'publication-payload01.json').write_text(json.dumps(dict(path=str(D),files=len(files)+1,bytes=sum(p.stat().st_size for p in D.rglob('*') if p.is_file()),handwritten=hand,generated=generated),indent=2)+'\n')
print(dict(files=len(files)+1,handwritten=len(hand),generated=len(generated)))

