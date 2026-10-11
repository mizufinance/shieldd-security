"""Review selected inherited custom imports and immutable machine guard sources."""
from pathlib import Path
import ast,hashlib,json,re,importlib.util
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');J=W/'resumed-orchestration-20261009-01/first-epoch60-61-review01';G=W/'shared-build-handoff';P=W/'mac-first-epoch60-61-kernel-result01'
spec=importlib.util.spec_from_file_location('source_header',J.parent/'prepare_source_closure.py');header=importlib.util.module_from_spec(spec);spec.loader.exec_module(header)
fresh={e['module']:e for e in json.loads((P/'qualified-modules01.json').read_bytes())};pub=json.loads((J.parent/'source-integration-20261011-01/mac-source-closure523.json').read_bytes())['custom_sources']
checked={}
def read(v):
 key=(v['path'],v['bytes'],v['sha256'])
 if key not in checked:
  p=Path(v['path']);assert p.is_file()and not p.is_symlink(),p
  b=p.read_bytes();assert len(b)==v['bytes']and hashlib.sha256(b).hexdigest()==v['sha256'],p;checked[key]=b
 return checked[key]
def imports(b):return [n for n in header.imports(b.decode())if n.startswith('ShielddSecurity.')]
expectedguards={'264a038f756299a3f69e4c29e1419f5ec1e3f6deb7f26fa0975157fede495eaa'}
accepted=(W/'mac-assertion-provider50-execution09/maintained/guard.py').read_bytes()
for n in ['14','16']:assert (W/('mac-full-arithmetic45-execution'+n)/'maintained/guard.py').read_bytes()==accepted
physical={'threads':1,'heap_MiB':2048,'group_rss_bytes':4294967296,'module_seconds':240,'minimum_free_RAM_percent':15,'minimum_free_disk_bytes':2147483648,'heartbeats':900000,'recdepth':8192}
configs={};associations={};resolutions=[]
for name,e in fresh.items():
 root=Path(e['receipt']['path']).parents[2]
 if root not in configs:
  c=json.loads((root/'config01.json').read_bytes());assert c['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
  for k,v in physical.items():assert c['limits'][k]==v,(root,k)
  maintained=Path(c['maintained']);assert {x.name for x in maintained.iterdir()}=={'guard.py','prepare.py'}
  for x in maintained.iterdir():read(c['static_records'][str(x)])
  gh=hashlib.sha256((root/'maintained/guard.py').read_bytes()).hexdigest();assert gh in expectedguards
  configs[root]=(c,gh)
 c,gh=configs[root]
 read(c['official'])
 own=json.loads(read(e['receipt']));assert own['cleanup']['clean'] and own['exit']==0 and own['lean_seconds']<=240 and own['peak_group_rss']<=4294967296,name
 assert own['inherited_closure']==c['closure']and own['official_manifest']==c['official'],name
 assert c['lean_environment']['LEAN_NUM_THREADS']=='1' and c['lean_environment']['LEAN_PATH']==':'.join(c['lean_path']),name
 source_root=Path(c['modules'][name].get('source_root',c['source_root']));objects=list(e['objects'].values());assert len(objects)==1
 assert own['command']==[c['lean'],'-j1','-M2048','-R',str(source_root),'-o',objects[0]['path'],e['source']['path']],name
 assert Path(e['source']['path'])==source_root/'ShielddSecurity'/(name+'.lean'),name
 for observation in [own['preflight'],own['postflight'],*own['observations']]:
  assert observation['free_memory_percent']>=15 and observation['free_disk_bytes']>=2147483648,name
 pool=json.loads(read(c['closure']))['modules'];pool.update(c['qualified_batch_imports'])
 for local,fe in fresh.items():
  if local in pool:continue
  objs=list(fe['objects'].values());assert len(objs)==1
  pool[local]={'source':fe['source'],'object':objs[0],'receipt':fe['receipt'],'custom_imports':imports(read(fe['source'])),'current_slots':{'.olean':objs[0]}}
 seen=set()
 def visit(n):
  if n in seen:return
  seen.add(n);m=pool[n];sb=read(m['source']);read(m['object']);r=json.loads(read(m['receipt']));assert r['status']=='passed'and r['exit']==0,n
  if 'source' in r:
   assert r['source']==m['source']and m['object']in r['objects'].values(),n
  else:
   assert r['source_sha256']==m['source']['sha256']and r['object_sha256']==m['object']['sha256'],n
  for slot in m['current_slots'].values():
   if slot is not None:read(slot)
  actual=imports(sb);assert actual==m['custom_imports'],n
  candidate=None
  for lp in c['lean_path']:
   package=Path(lp)/'ShielddSecurity'
   if package.is_dir()or(Path(lp)/'ShielddSecurity.olean').is_file():candidate=package/(n+'.olean');break
  assert candidate is not None and candidate.resolve()==Path(m['object']['path']).resolve(),(name,n)
  if n in fresh:assert m['source']==fresh[n]['source'],n
  elif n=='CapturedArithmetic45B0000':
   assert m['source']['sha256']=='e02032f01e15886e2d0f9be492978c7ed12ab7a7a63e75d794c0ae189dcdf05d' and m['source']['bytes']==94793
  else:
   assert n in pub,n
   assert m['source']['sha256']==pub[n]['sha256']and m['source']['bytes']==pub[n]['bytes'],n
   assert any((G/z).is_file()and (G/z).read_bytes()==sb for z in pub[n]['published_paths']),n
  association={'source':m['source'],'object':m['object'],'receipt':m['receipt'],'prior_published':n in pub,'selected_inherited_unpublished_support':n=='CapturedArithmetic45B0000'}
  if n in associations:assert associations[n]==association,n
  associations[n]=association
  for child in actual:visit(child.removeprefix('ShielddSecurity.'))
 for dep in imports(read(e['source'])):visit(dep.removeprefix('ShielddSecurity.'))
 resolutions.append({'module':name,'custom_dependencies':sorted(seen),'guard_sha256':gh})
result={'scope':'Selected custom source/object/receipt/load association review; inherited receipts are not freshly replayed','fresh_modules':2,'fresh_reports':42,'custom_associations':associations,'resolution':resolutions,'execution_configs':[{'path':str(root),'guard_sha256':v[1],'physical_limits':physical}for root,v in configs.items()],'pins_rehashed':len(checked),'new_guard_delta':'Guard bytes identical to accepted assertion-provider50 execution09. All physical protections unchanged.','scope_boundary':'First epoch bounded field representation and zero/inverse hint assertions. Canonical natural meaning, all remaining assertions, native refinement and full Transfer remain open.','full_transfer':'OPEN'}
(J/'import-guard-review01.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'modules':2,'associations':len(associations),'pins':len(checked),'prior':sum(a['prior_published']for a in associations.values()),'guards':sorted({v[1]for v in configs.values()})}))
