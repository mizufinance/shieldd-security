from pathlib import Path
import json,hashlib,shutil,sys
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');J=R/'resumed-orchestration-20261009-01';G=R/'shared-build-handoff'
key=sys.argv[1];spec={'uniqueness49':('mac-arithmetic-uniqueness49-kernel-result01','arithmetic-uniqueness49-review01','arithmetic-uniqueness49')};packet,review,name=spec[key];P=R/packet;V=J/review;D=G/'handoffs/transfer-20261009/sources/mac'/name;assert not D.exists();D.mkdir(parents=True)
def copy(p,relative):
 d=D/relative;d.parent.mkdir(parents=True,exist_ok=True)
 if d.exists():assert d.read_bytes()==p.read_bytes()
 else:shutil.copyfile(p,d)
for p in P.glob('*.json'):copy(p,Path('provenance')/p.name)
copy(P/'seal.py',Path('maintained')/packet/'seal.py')
q=json.loads((P/'qualified-modules01.json').read_bytes());entries=q if isinstance(q,list)else[q]if 'module'in q else list(q.values())
for e in entries:
 copy(Path(e['source']['path']),Path('sources/ShielddSecurity')/(e['module']+'.lean'));p=Path(e['receipt']['path']);copy(p,Path('receipts/accepted')/p.name)
for x in json.loads((P/'maintained-references01.json').read_bytes()):
 p=Path(x['path']);b=p.read_bytes();assert len(b)==x['bytes']and hashlib.sha256(b).hexdigest()==x['sha256'];copy(p,Path('maintained')/p.relative_to(R))
for name in ['audit_endpoint.py','audit-result01.json','generator-inventory-review01.json','verify_imports_guards.py','import-guard-review02.json','endpoint-review.md']:copy(V/name,Path('parent-review')/name)
copy(Path(__file__),Path('parent-review/prepare_publication.py'))
execution=json.loads((P/'execution-census01.json').read_bytes())
def history(x):
 if isinstance(x,dict):
  for k,v in x.items():
   if k in ['receipt','source']and isinstance(v,dict)and set(['path','bytes','sha256'])<=v.keys():
    p=Path(v['path'])
    if p.is_file()and p.suffix in ['.json','.lean']:copy(p,Path('provenance/history')/p.relative_to(R))
   else:history(v)
 elif isinstance(x,list):
  for y in x:history(y)
history(execution)
(D/'README.md').write_text('Scoped reviewed proof source/evidence for runtime844389ee069e1fb2e576708842d0b389b4d9a44a. See parent-review/endpoint-review.md for exact premises and remaining full Transfer obligations. Objects, toolchains, caches, captured workspaces and raw compiler logs are excluded. Full Transfer remains open.\n')
records=[dict(path=str(p.relative_to(D)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())for p in sorted(D.rglob('*'))if p.is_file()];(D/'publication-manifest01.json').write_text(json.dumps(dict(kind='exact scoped source/evidence transport; no parent Lean replay',source_packet=str(P),files=records,full_transfer='OPEN'),indent=2)+'\n');(V/'publication-payload01.json').write_text(json.dumps(dict(path=str(D),files=len(records)+1,bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file())),indent=2)+'\n');print(json.dumps(dict(name=name,files=len(records)+1,bytes=sum(p.stat().st_size for p in D.rglob('*')if p.is_file()))))
