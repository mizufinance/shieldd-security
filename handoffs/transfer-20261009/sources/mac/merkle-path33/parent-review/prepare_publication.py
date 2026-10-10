from pathlib import Path
import json,hashlib,shutil
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');J=Path(__file__).resolve().parent;P=R/'mac-merkle-path33-kernel-result01'
D=R/'shared-build-handoff/handoffs/transfer-20261009/sources/mac/merkle-path33'
assert not D.exists();D.mkdir(parents=True)
copied={}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(source,relative):
 target=D/relative;target.parent.mkdir(parents=True,exist_ok=True)
 if target.exists():assert target.read_bytes()==source.read_bytes()
 else:shutil.copyfile(source,target)
 copied[str(relative)]=dict(original=str(source),bytes=target.stat().st_size,sha256=digest(target))
for p in sorted(P.glob('*.json')):copy(p,Path('provenance')/p.name)
copy(P/'seal.py',Path('maintained/mac-merkle-path33-kernel-result01/seal.py'))
mods=json.loads((P/'qualified-modules01.json').read_bytes())
for name,entry in mods.items():
 copy(Path(entry['source']['path']),Path('sources/ShielddSecurity')/(name+'.lean'))
 rp=Path(entry['receipt']['path']);copy(rp,Path('receipts/accepted')/rp.name)
for pin in json.loads((P/'maintained-references01.json').read_bytes()):
 p=Path(pin['path']);assert p.stat().st_size==pin['bytes']and digest(p)==pin['sha256']
 copy(p,Path('maintained')/p.relative_to(R))
for failure in json.loads((P/'execution-census01.json').read_bytes())['failed_predecessors']:
 for key in ['receipt','source']:
  p=Path(failure[key]['path']);copy(p,Path('provenance/failed')/p.relative_to(R))
for name in ['review_regeneration.py','audit-result01.json','endpoint-regeneration01.json','anchor-capture-review01.json','endpoint-review.md','prepare_publication.py']:
 copy(J/name,Path('parent-review')/name)
copy(J.parent/'merkle-family32-selection-bodies-review01/audit_endpoint.py',Path('parent-review/audit_endpoint.py'))
copy(J.parent/'merkle-family32-binding-review01/preliminary-regeneration01.json',Path('parent-review/binding-preliminary-regeneration01.json'))
copy(J.parent/'merkle-family32-binding-review01/regeneration01/original-generate.py',Path('parent-review/binding-original-generate.py'))
copy(J.parent/'merkle-family32-binding-review01/regeneration01/generate.py',Path('parent-review/binding-scratch-generate.py'))
(D/'README.md').write_text('Scoped sixteen-level field-path and anchor proof for pinned runtime 844389ee069e1fb2e576708842d0b389b4d9a44a. See parent-review/endpoint-review.md for verified premises and open full Transfer obligations. This source/evidence transport excludes compiler caches, objects, raw compiler logs, and captured workspaces. Maintained recipes retain their exact producer paths; portable full generation remains open.\n')
files=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=digest(p))for p in sorted(D.rglob('*'))if p.is_file()]
with(D/'publication-manifest01.json').open('x')as f:json.dump(dict(schema=1,kind='exact scoped source/evidence transport; no parent Lean replay',source_packet=str(P),files=files),f,indent=2);f.write('\n')
with(J/'publication-payload01.json').open('x')as f:json.dump(dict(path=str(D),files=len(files)+1,bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),copies=copied),f,indent=2);f.write('\n')
print(json.dumps(dict(files=len(files)+1,bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()))))
