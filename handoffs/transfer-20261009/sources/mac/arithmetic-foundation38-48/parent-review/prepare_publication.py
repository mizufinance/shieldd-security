from pathlib import Path
import json,hashlib,shutil
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');V=W/'resumed-orchestration-20261009-01/arithmetic-foundation48-review01';G=W/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/mac/arithmetic-foundation38-48'
PACKETS=['mac-indexed-arithmetic38-kernel-result02','mac-arithmetic-coefficients39-kernel-result01','mac-indexed-arithmetic43-kernel-result01','mac-arithmetic-block44-kernel-result02','mac-arithmetic-fixed48-kernel-result01']
assert not D.exists();D.mkdir(parents=True)
def copy(p,r):
 t=D/r;t.parent.mkdir(parents=True,exist_ok=True)
 if t.exists():assert t.read_bytes()==p.read_bytes()
 else:shutil.copyfile(p,t)
def pin(x):
 p=Path(x['path']);b=p.read_bytes();assert len(b)==x['bytes']and hashlib.sha256(b).hexdigest()==x['sha256'];return p
def history(x):
 if isinstance(x,dict):
  for k,v in x.items():
   if k in ['source','receipt']and isinstance(v,dict)and {'path','sha256','bytes'}<=v.keys():
    p=pin(v)
    if p.suffix in ['.lean','.json']:copy(p,Path('provenance/history')/p.relative_to(W))
   else:history(v)
 elif isinstance(x,list):
  for v in x:history(v)
modules=[]
for n in PACKETS:
 P=W/n
 for p in P.glob('*.json'):copy(p,Path('provenance')/n/p.name)
 copy(P/'seal.py',Path('maintained')/n/'seal.py')
 for e in json.loads((P/'qualified-modules01.json').read_text()):
  modules.append(e['module']);copy(pin(e['source']),Path('sources/ShielddSecurity')/(e['module']+'.lean'))
  rp=pin(e['receipt']);copy(rp,Path('receipts/accepted')/rp.relative_to(W))
 for ref in json.loads((P/'maintained-references01.json').read_text()):
  p=pin(ref);copy(p,Path('maintained')/p.relative_to(W))
 history(json.loads((P/'execution-census01.json').read_text()))
 d=json.loads((V/'declaration-inventory01.json').read_text());d['kind']='Independent explicit public declaration inventory, accepted scoped arithmetic helpers and six captured probes';d['modules']=[m for m in d['modules']if m['module']in modules];d['declarations']=sum(len(m['lexical_declarations'])for m in d['modules'])
 (V/'accepted-declaration-inventory02.json').write_text(json.dumps(d,indent=2)+'\n')
assert len(modules)==21 and d['declarations']==277
regen=json.loads((V/'generator-regeneration-review02.json').read_text());regen['roots']=[x for x in regen['roots']if not x['root'].endswith('mac-arithmetic-first40-group47-source02')];(V/'accepted-generator-regeneration02.json').write_text(json.dumps(regen,indent=2)+'\n')
for n in ['mac-indexed-arithmetic38-kernel-result02-audit01.json','mac-arithmetic-coefficients39-kernel-result01-audit01.json','mac-indexed-arithmetic43-kernel-result01-audit01.json','mac-arithmetic-block44-kernel-result02-audit01.json','audit-result01.json','accepted-declaration-inventory02.json','accepted-generator-regeneration02.json','capture-replay-review02.json','coefficient-dispatch-review01.json','check_coefficient_dispatch.py','verify_declarations.py','verify_imports_guards.py','import-guard-review02.json','guard-delta-review01.json','endpoint-review.md','prepare_publication.py']:
 copy(V/n,Path('parent-review')/n)
copy(W/'resumed-orchestration-20261009-01/fresh-arithmetic35-review01/audit_endpoint.py',Path('parent-review/audit_endpoint.py'))
(D/'README.md').write_text('Reviewed scoped arithmetic helpers, coefficient lookup sources and six captured row probes for exact runtime844389ee069e1fb2e576708842d0b389b4d9a44a. See parent-review/endpoint-review.md. This package excludes the first40/full599 arithmetic aggregates and does not certify full Transfer. Original producer references preserve execution identities. No objects, caches, toolchains, capture databases or raw compiler logs are included. Final portable combined integration and replay remain open.\n')
records=[{'path':str(p.relative_to(D)),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}for p in sorted(D.rglob('*'))if p.is_file()]
(D/'publication-manifest01.json').write_text(json.dumps({'kind':'Exact reviewed scoped source/evidence transport; no parent Lean replay','producer_packets':PACKETS,'modules':modules,'reports':277,'files':records,'full_transfer':'OPEN'},indent=2)+'\n')
r={'path':str(D),'files':len(records)+1,'bytes':sum(p.stat().st_size for p in D.rglob('*')if p.is_file()),'modules':21,'reports':277}
(V/'publication-payload02.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))

