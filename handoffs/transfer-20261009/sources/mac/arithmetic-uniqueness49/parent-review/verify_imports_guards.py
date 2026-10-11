from pathlib import Path
import json,hashlib,re,ast
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');V=W/'resumed-orchestration-20261009-01/arithmetic-uniqueness49-review01';G=W/'shared-build-handoff'
PACKETS=['mac-arithmetic-uniqueness49-kernel-result01']
pub=json.loads((W/'resumed-orchestration-20261009-01/arithmetic-foundation48-review01/source-closure02.json').read_text())['custom_sources']
fresh={}
for p in PACKETS:
 for e in json.loads((W/p/'qualified-modules01.json').read_text()):fresh[e['module']]=e
checked={}
def read(x):
 p=Path(x['path']);key=(str(p),x['sha256'],x['bytes'])
 if key not in checked:
  b=p.read_bytes();assert len(b)==x['bytes']and hashlib.sha256(b).hexdigest()==x['sha256'],p
  checked[key]=b
 return checked[key]
def imports(b):return re.findall(r'(?m)^import (ShielddSecurity\.[A-Za-z0-9_.]+)\s*$',b.decode())
baseline=(W/'mac-fresh-arithmetic35-source04/maintained/guard.py').read_bytes()
acceptedguards={hashlib.sha256(baseline).hexdigest(), '06bb514a7ae8e1120283ad79250eb14752e554767762a9896cc969b982009b0e','4e469e962b8a0d6e4b7b5f869415e4958bd5e95e2d6280c5c87dff1d5306c4c7'}
basefn={n.name:n for n in ast.parse(baseline).body if isinstance(n,ast.FunctionDef)}
resolution=[];associations={};configs={}
for name,e in fresh.items():
 root=Path(e['source']['path']).parents[2];c=json.loads((root/'config01.json').read_text());configs[str(root)]=c
 assert c['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
 lim=c['limits']
 for k,v in {'threads':1,'heap_MiB':2048,'group_rss_bytes':4294967296,'module_seconds':240,'minimum_free_RAM_percent':15,'minimum_free_disk_bytes':2147483648}.items():assert lim[k]==v,(name,k)
 gb=(root/'maintained/guard.py').read_bytes();gh=hashlib.sha256(gb).hexdigest();assert gh in acceptedguards,(name,gh)
 funcs={n.name:n for n in ast.parse(gb).body if isinstance(n,ast.FunctionDef)}
 for fn in basefn:
  if fn not in ['bounds','direct_imports','execute','fixed_check','launch_reserve']:assert ast.dump(basefn[fn])==ast.dump(funcs[fn]),(name,fn)
 pool=json.loads(read(c['closure']))['modules'];pool.update(c['qualified_batch_imports'])
 for local in c['modules']:
  if local in pool:continue
  fe=fresh[local];objs=list(fe['objects'].values());assert len(objs)==1
  pool[local]={'source':fe['source'],'object':objs[0],'receipt':fe['receipt'],'custom_imports':imports(read(fe['source'])),'current_slots':{'.olean':objs[0]}}
  if local!=name and 'ShielddSecurity.'+'ShielddSecurity.'+local in imports(read(e['source'])):assert c['order'].index(local)<c['order'].index(name)
 seen=set()
 def visit(n):
  if n in seen:return
  seen.add(n);m=pool[n];sb=read(m['source']);read(m['object']);r=json.loads(read(m['receipt']));assert r['status']=='passed',n
  for slot in m['current_slots'].values():
   if slot is not None:read(slot)
  actual=imports(sb);assert actual==m['custom_imports'],n
  candidate=None
  for lp in c['lean_path']:
   package=Path(lp)/'ShielddSecurity'
   if package.is_dir() or (Path(lp)/'ShielddSecurity.olean').is_file():
    candidate=package/(n+'.olean');break
  assert candidate and candidate.resolve()==Path(m['object']['path']).resolve(),(name,n,candidate)
  if n in fresh:assert m['source']==fresh[n]['source'],n
  elif n in pub:
   assert m['source']['sha256']==pub[n]['sha256'] and m['source']['bytes']==pub[n]['bytes'],n
   assert any((G/z).is_file()and (G/z).read_bytes()==sb for z in pub[n]['published_paths']),n
  else:
   assert n in ['CompilerFreshArithmetic35','CompilerIndexedCoverage36'],n
   p=G/'handoffs/transfer-20261009/sources/mac/fresh-arithmetic35/sources/ShielddSecurity'/(n+'.lean');assert p.read_bytes()==sb,n
  associations[n]={'source':m['source'],'object':m['object'],'receipt':m['receipt'],'prior_published':n not in fresh}
  for child in actual:visit(child.removeprefix('ShielddSecurity.'))
 for dep in imports(read(e['source'])):visit(dep.removeprefix('ShielddSecurity.'))
 resolution.append({'module':name,'custom_dependencies':sorted(seen),'guard_sha256':gh,'physical_limits':{k:lim[k]for k in ['threads','heap_MiB','group_rss_bytes','module_seconds','minimum_free_RAM_percent','minimum_free_disk_bytes']}})
r={'scope':'Selected custom source/object/receipt/load associations and physical safeguards; no imported module fresh kernel replay','fresh_modules':len(fresh),'fresh_reports':6,'custom_associations':associations,'resolution':resolution,'pins_rehashed':len(checked),'full_transfer':'OPEN','first40_aggregate':'Separate pre-review, excluded from this scoped acceptance'}
(V/'import-guard-review02.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'modules':len(fresh),'associations':len(associations),'pins':len(checked),'prior':sum(a['prior_published']for a in associations.values())}))
