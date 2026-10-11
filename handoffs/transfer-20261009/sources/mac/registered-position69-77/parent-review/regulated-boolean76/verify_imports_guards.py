"""Review selected inherited custom imports and immutable machine guard sources."""
from pathlib import Path
import ast,hashlib,json,re,importlib.util
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');J=W/'resumed-orchestration-20261009-01/regulated-boolean76-review01';G=W/'shared-build-handoff';P=W/'mac-regulated-boolean76-kernel-result01'
spec=importlib.util.spec_from_file_location('source_header',J.parent/'prepare_source_closure.py');header=importlib.util.module_from_spec(spec);spec.loader.exec_module(header)
fresh={}
for task_packet in ['mac-full-arithmetic45-kernel-result01','mac-full-captured-epoch64-kernel-result01','mac-registry-epoch-semantic66-kernel-result01','mac-global-zero-completion68-kernel-result01','mac-registered-audit71-kernel-result01','mac-global-registered75-kernel-result01','mac-regulated-boolean76-kernel-result01','mac-global-position77-kernel-result01']:
 for entry in json.loads((W/task_packet/'qualified-modules01.json').read_bytes()):
  if entry['name'] in fresh:assert fresh[entry['name']]==entry
  fresh[entry['name']]=entry
active_fresh={e['name']:e for e in json.loads((P/'qualified-modules01.json').read_bytes())}
reports=json.loads((J/'audit-result01.json').read_bytes())['declarations']
pub=json.loads((J.parent/'source-integration-20261011-01/mac-source-closure1146.json').read_bytes())['custom_sources']
checked={}
def read(v):
 key=(v['path'],v['bytes'],v['sha256'])
 if key not in checked:
  p=Path(v['path']);assert p.is_file()and not p.is_symlink(),p
  with p.open('rb')as f:digest=hashlib.file_digest(f,'sha256').hexdigest()
  assert p.stat().st_size==v['bytes']and digest==v['sha256'],p
  checked[key]=b'' if '.olean' in p.name else p.read_bytes()
 return checked[key]
def imports(b):return [n for n in header.imports(b.decode())if n.startswith('ShielddSecurity.')]
expectedguards={'e93d97e6af517d01ee08e72912b145725117ca93c7d2d88fdf70a93d96fc5b04','fe4d35070ed16111f03817a98596eaeb03b9d5730c4fe726d5a4c29f8ae343ab','06bb514a7ae8e1120283ad79250eb14752e554767762a9896cc969b982009b0e','4e469e962b8a0d6e4b7b5f869415e4958bd5e95e2d6280c5c87dff1d5306c4c7','aa0d3c1a34182a2408d65956e5bd28f4998307b6e307246f4ee722fe5761141b','a4bca2487c7d7472dc7aa53195f2f194147c210a2f46119f1b3fe905d6a72c84','264a038f756299a3f69e4c29e1419f5ec1e3f6deb7f26fa0975157fede495eaa','2c608925518b5a6a4f828cb532e535979fd45c1e59077f4c9c070b97f231b548'}
expectedguards.update({'b7d1ce67b936b0cdcd6e1805fe299eee42f3f49cbc64f2d6fd9ab15deb829dce','bb83b7be30a6bc61e0c5fe80318f66d2661077114171d33a8bd501543d757888'})
physical={'threads':1,'heap_MiB':2048,'group_rss_bytes':4294967296,'module_seconds':240,'minimum_free_RAM_percent':15,'minimum_free_disk_bytes':2147483648,'heartbeats':900000,'recdepth':8192}
configs={};associations={};resolutions=[]
for name,e in active_fresh.items():
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
  else:
   assert n in pub,n
   assert m['source']['sha256']==pub[n]['sha256']and m['source']['bytes']==pub[n]['bytes'],n
   assert any((G/z).is_file()and (G/z).read_bytes()==sb for z in pub[n]['published_paths']),n
  association={'source':m['source'],'object':m['object'],'receipt':m['receipt'],'prior_published':n not in fresh}
  if n in associations:assert associations[n]==association,n
  associations[n]=association
  for child in actual:visit(child.removeprefix('ShielddSecurity.'))
 for dep in imports(read(e['source'])):visit(dep.removeprefix('ShielddSecurity.'))
 resolutions.append({'module':name,'custom_dependencies':sorted(seen),'guard_sha256':gh})
result={'scope':'Selected custom source/object/receipt/load association review; inherited receipts are not freshly replayed','qualified_modules':len(active_fresh),'complete_reports':reports,'custom_associations':associations,'resolution':resolutions,'execution_configs':[{'path':str(root),'guard_sha256':v[1],'physical_limits':physical}for root,v in configs.items()],'pins_rehashed':len(checked),'new_guard_delta':'Original guard revisions and byte deltas reviewed separately; active source parsing, exact-digest header memoization, removal of redundant pre-layout checks while retaining the held-lock PACKAGE check, and finite on-disk metadata thresholds only. All physical protections unchanged.','scope_boundary':'Selected actual-row/registry/zero-test joins only; full Transfer/native refinement remains OPEN','full_transfer':'OPEN'}
(J/'import-guard-review01.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'modules':len(active_fresh),'associations':len(associations),'pins':len(checked),'prior':sum(a['prior_published']for a in associations.values()),'guards':sorted({v[1]for v in configs.values()})}))
