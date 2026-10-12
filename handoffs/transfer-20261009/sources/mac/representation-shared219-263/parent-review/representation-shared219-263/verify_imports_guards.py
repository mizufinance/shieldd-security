"""Review selected inherited custom imports and immutable machine guard sources."""
from pathlib import Path
import ast,hashlib,json,re,importlib.util
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');J=W/'resumed-orchestration-20261009-01/representation-shared219-263-review01';G=W/'shared-build-handoff';P=W/'mac-representation-shared219-263-kernel-result01'
spec=importlib.util.spec_from_file_location('source_header',J.parent/'prepare_source_closure.py');header=importlib.util.module_from_spec(spec);spec.loader.exec_module(header)
pspec=importlib.util.spec_from_file_location('preserved_configs',J.parent/'read_preserved_mac_config16.py');preserved=importlib.util.module_from_spec(pspec);pspec.loader.exec_module(preserved)
fresh={}
for task_packet in ['mac-full-arithmetic45-kernel-result01','mac-full-captured-epoch64-kernel-result01','mac-registry-epoch-semantic66-kernel-result01','mac-global-zero-completion68-kernel-result01','mac-registered-audit71-kernel-result01','mac-global-registered75-kernel-result01','mac-regulated-boolean76-kernel-result01','mac-global-position77-kernel-result01','mac-subgroup-source81-kernel-result01','mac-four-subgroups82-kernel-result01','mac-subgroup-closure83-kernel-result01','mac-first-subgroup-constructor85-kernel-result01','mac-four-subgroup-constructor89-kernel-result01','mac-global-subgroup90-kernel-result01','mac-regulated-asset95-96-kernel-result01','mac-registry-value-range97-kernel-result01','mac-registry-value-global98-99-kernel-result01','mac-comparison100-101-kernel-result01','mac-comparison102-104-kernel-result01','mac-value-canonical105-108-kernel-result01','mac-asset-canonical109-113-kernel-result01','mac-next-canonical114-118-kernel-result01','mac-high-limb119-124-kernel-result01','mac-high-zero125-128-kernel-result01','mac-low-limb129-132-kernel-result01','mac-next-high-low133-144-kernel-result01','mac-registry-gap145-147-kernel-result01','mac-comparison-sound148-152-kernel-result01','mac-gap-sound153-156-kernel-result01','mac-canonical-decode157-159-kernel-result01','mac-registry-canonical-order160-164-kernel-result01','mac-anchor-indexed165-166-kernel-result01','mac-indexed-copy-stream171-kernel-result01','mac-call04-global168-169-kernel-result01','mac-indexed-coverage172-174-178-179-kernel-result01','mac-prior-global170-kernel-result01','mac-merkle-global-body181-kernel-result01','mac-natural-registry183-194-kernel-result01','mac-merkle-bits188-pilot182-kernel-result01','mac-registry-subgroup195-203-kernel-result01']:
 for entry in json.loads((W/task_packet/'qualified-modules01.json').read_bytes()):
  if entry['name'] in fresh:assert fresh[entry['name']]==entry
  fresh[entry['name']]=entry
for e in json.loads((W/'mac-threecall-global-binding173-kernel-result01/source-object-receipt01.json').read_bytes()):
 e=dict(e);e['name']=e['module'];e['objects']=json.loads(Path(e['receipt']['path']).read_bytes())['objects'];fresh[e['name']]=e
for packet in [W/'mac-canonical-word215-kernel-result01',W/'mac-word-foundation210-214-kernel-result01',J.parent/'word-foundation210-214-review01/boolean207-reference-packet01']:
 for e in json.loads((packet/'source-object-receipt01.json').read_bytes()):
  e=dict(e);e['name']=e['module'];e['objects']=json.loads(Path(e['receipt']['path']).read_bytes())['objects'];fresh[e['name']]=e
for e in sum((json.loads((W/packet/'source-object-receipt01.json').read_bytes())for packet in ['mac-captured-canonical217-kernel-result01','mac-boolean208-209-kernel-result01','mac-word211-213-kernel-result01','mac-shared-word-flags220-kernel-result01','mac-shared-word-witness221-kernel-result01']),[]):
 e=dict(e);e['name']=e['module'];e['objects']=json.loads(Path(e['receipt']['path']).read_bytes())['objects'];fresh[e['name']]=e
for packet in [W/'mac-merkle-dense233-241-kernel-result01',W/'mac-registry-global175-176-kernel-result01',W/'mac-merkle-first186-kernel-result01',W/'mac-merkle-level0-243-kernel-result01',W/'mac-merkle-level1-243-kernel-result01',W/'mac-merkle-level2-243-kernel-result01',W/'mac-merkle-level3-243-kernel-result01',W/'mac-merkle-level4-243-kernel-result01',W/'mac-merkle-level5-243-kernel-result01',W/'mac-merkle-level6-243-kernel-result01',W/'mac-merkle-level7-243-kernel-result01',W/'mac-merkle-level8-243-kernel-result01',W/'mac-merkle-level9-243-kernel-result01',W/'mac-merkle-level10-243-kernel-result01',W/'mac-merkle-level11-243-kernel-result01',W/'mac-merkle-level12-243-kernel-result01',W/'mac-merkle-level13-243-kernel-result01',W/'mac-merkle-level14-243-kernel-result01',W/'mac-merkle-path-global187-kernel-result01',W/'mac-arithmetic-selection252-254-kernel-result01',W/'mac-candidate-ordered250-256-kernel-result01',W/'mac-integer-root-packed190-257-kernel-result01',W/'mac-natural-root-indexed196-260-kernel-result01',W/'mac-registry-candidate205-255-kernel-result01',W/'mac-candidate-fullpath258-262-kernel-result01']:
 for e in json.loads((packet/'source-object-receipt01.json').read_bytes()):
  e=dict(e);e['name']=e['module'];e['objects']=json.loads(Path(e['receipt']['path']).read_bytes())['objects'];fresh[e['name']]=e
for e in json.loads((J.parent/'merkle-dense233-241-review01/imported-qualified-originals01.json').read_bytes()):
 e=dict(e);e['name']=e['module'];e['objects']=json.loads(Path(e['receipt']['path']).read_bytes())['objects'];fresh[e['name']]=e
active_fresh={}
for e in json.loads((P/'source-object-receipt01.json').read_bytes()):
 e=dict(e);e['name']=e['module'];e['objects']=json.loads(Path(e['receipt']['path']).read_bytes())['objects']
 if e['name'] in fresh:assert fresh[e['name']]['source']==e['source']
 fresh[e['name']]=e;active_fresh[e['name']]=e
reports=json.loads((J/'audit-result01.json').read_bytes())['declarations']
pub=json.loads((J.parent/'source-integration-20261011-01/mac-source-closure2614.json').read_bytes())['custom_sources']
checked={}
def read(v):
 key=(v['path'],v['bytes'],v['sha256'])
 if key not in checked:
  p=Path(v['path'])
  if not p.exists():
   checked[key]=preserved.read_config(p,v);return checked[key]
  assert p.is_file()and not p.is_symlink(),p
  with p.open('rb')as f:digest=hashlib.file_digest(f,'sha256').hexdigest()
  assert p.stat().st_size==v['bytes']and digest==v['sha256'],p
  checked[key]=b'' if '.olean' in p.name else p.read_bytes()
 return checked[key]
def imports(b):return [n for n in header.imports(b.decode())if n.startswith('ShielddSecurity.')]
expectedguards={'e93d97e6af517d01ee08e72912b145725117ca93c7d2d88fdf70a93d96fc5b04','fe4d35070ed16111f03817a98596eaeb03b9d5730c4fe726d5a4c29f8ae343ab','06bb514a7ae8e1120283ad79250eb14752e554767762a9896cc969b982009b0e','4e469e962b8a0d6e4b7b5f869415e4958bd5e95e2d6280c5c87dff1d5306c4c7','aa0d3c1a34182a2408d65956e5bd28f4998307b6e307246f4ee722fe5761141b','a4bca2487c7d7472dc7aa53195f2f194147c210a2f46119f1b3fe905d6a72c84','264a038f756299a3f69e4c29e1419f5ec1e3f6deb7f26fa0975157fede495eaa','2c608925518b5a6a4f828cb532e535979fd45c1e59077f4c9c070b97f231b548'}
expectedguards.update({'d28ca27c67c26fc6bb8b71c83a98e78120a38895b6ede20cbb98d42860b4fa57','92c62c3c35fb636851a85ef3ddeaaa9185df6f40ffe2ef26a8ad3b3397634076','085dbdfa18f8ac859be613588d4ca1ed2ad2436fbf5d02c336654934bb795825','085dbdfa18f8ac859be613588d4ca1ed2ad2436fbf5d02c336654934bb795825','b7d1ce67b936b0cdcd6e1805fe299eee42f3f49cbc64f2d6fd9ab15deb829dce','bb83b7be30a6bc61e0c5fe80318f66d2661077114171d33a8bd501543d757888'})
expectedguards.add('8eb31ea75351ea4bf2562b1a2a583294c69c73b57f0cfc44e14552e50fcb953c')
expectedguards.add('c89c57b55398743a1206490855d7960630636af66a8208533e85f62a6ac8bf47')
expectedguards.update({'76af92ea7008ad69071c5cb7e2e8458204d6e43c476b68b1babf08e01e518bca','6217fe1842defd749fbe03e34a46024234156c16f2a36a15ca58824b845c218c'})
expectedguards.update({'6136469756b71f179b33ac2e4f82ffa2c76eec63855c54aecea559201be9fbe3','ff6c299719ba874c19deba3f335e834c1d30a98bf57cad0840ddd96b9ec36a70','8a721a59a67eb2bf089ead277561be83a41be8557d61735c9fd8e3328cfc39ce','c4ad8921031707767f33c5445f0eb772a844e8690c511361104db31c0b04ef40'})
expectedguards.update({'0bd4749151b31367d41607e5960982c4258860c9fe1d2f51dbcc6d5dfc5e5f4b','df0817bc2c071171583d69a304bb25e108ae6f8e42048dbd2e135996f6bc606f'})
expectedguards.add('5be5100aa2e08c47fa2992ca8e88456727c76df829a6269cb49c158e25cddaf1')
expectedguards.update({'8843eb3854ca31545517a327c39fe7f185f0097b95fe21d3a0fa78351c3b1b30','2245839157e8064968f67c2f9e69976b06837b0760f4fce9bc0b7832a060b792'})
expectedguards.update({'695a7423e2ac2ceea3d676a1f658714555ed310eb5f3e19631be490655bf6d55','17f2d76d932b01a514d6f9a40c9a76c021565be2b8035e215790bc3845ce4286'})
phase=json.loads((J.parent/'mac-phase-metadata-guard-review12.json').read_bytes());assert phase['status']=='PASSED'
expectedguards.update(x['sha256'] for x in phase['guards'])
expectedguards.update({'9bfbeb27414e567b70a775d8e8386e302e8d9320e7605b306f051d4fbb90b7bd','b1b49d2a9dd537f8901283e142a66b74fca86b0cb349448c1774df6bfc28ef0c','cc900fcc6e04d03ceab5c14d686323fcce1cf9e45d597a4f591ee257cbf50bc0','8d158b110e0941a502750e1188ad6580ee7672eecdd2147a049ad077c5a97c2a'})
assert json.loads((J.parent/'mac-resource-preflight-guard-review18.json').read_bytes())['status']=='PASSED'
g=json.loads((J.parent/'mac-storage-map29-successor-guard-review21.json').read_bytes());assert g['status']=='PASSED';expectedguards.add(g['successor']['sha256'])
g=json.loads((J.parent/'mac-compact-config-guard-review22.json').read_bytes());assert g['status']=='PASSED';expectedguards.add(g['successor']['sha256'])
for review in ['mac-metadata-shape-bounds-guard-review23.json','mac-directory-census-guard-review24.json','mac-metadata-cap-guard-review25.json']:
 g=json.loads((J.parent/review).read_bytes());assert g['status']=='PASSED';expectedguards.add(g['successor']['sha256'])
for review in ['mac-archive-memo-absence-guard-review26.json','mac-raw-history-link-census-guard-review27.json']:
 g=json.loads((J.parent/review).read_text());assert g['status']=='PASSED';expectedguards.add(g['successor']['sha256'])
g=json.loads((J.parent/'mac-storage-map38-pin-guard-review135.json').read_text());assert g['status']=='PASSED';expectedguards.add(g['successor']['sha256'])
physical={'threads':1,'heap_MiB':2048,'group_rss_bytes':4294967296,'module_seconds':240,'minimum_free_RAM_percent':15,'minimum_free_disk_bytes':2147483648,'heartbeats':900000,'recdepth':8192}
configs={};associations={};resolutions=[]
g=json.loads((J.parent/'mac-carried-history-cache-guard-review28.json').read_text());assert g['status']=='PASSED';expectedguards.add(g['successor']['sha256'])
g=json.loads((J.parent/'mac-storage-map37-pin-review115.json').read_text());assert g['status']=='PASSED';expectedguards.add(g['successor_guard']['sha256'])
for name,e in active_fresh.items():
 root=Path(e['receipt']['path']).parents[2]
 if root not in configs:
  c=json.loads(preserved.read_config(root/'config01.json'));assert c['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
  for k,v in physical.items():assert c['limits'][k]==v,(root,k)
  maintained=Path(c['maintained']);assert {x.name for x in maintained.iterdir()}=={'guard.py','prepare.py'}
  for x in maintained.iterdir():read(c['static_records'][str(x)])
  gh=hashlib.sha256((root/'maintained/guard.py').read_bytes()).hexdigest();assert gh in expectedguards or gh=='d0d0d2c9058d660591e40eac1aded7106d3c9d2ce94b219f17f115bd2c036af8'
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
result={'scope':'Selected custom source/object/receipt/load association review; inherited receipts are not freshly replayed','qualified_modules':len(active_fresh),'complete_reports':reports,'custom_associations':associations,'resolution':resolutions,'execution_configs':[{'path':str(root),'guard_sha256':v[1],'physical_limits':physical}for root,v in configs.items()],'pins_rehashed':len(checked),'independent_guard_successor_review':['mac-archived-metadata-successors-review05.json','mac-metadata-cache-guard-review06.json','mac-archive-map18-guard-review07.json','mac-metadata-phase-cache-guard-review08.json','mac-successor-guard-review09.json','mac-header-cache-guard-review10.json','mac-phase-metadata-guard-review12.json'], 'new_guard_delta':'Guard217..223 independently reviewed14..18; exact source pins, phase hash close, exact DATA alias, RAM/disk early admission with full immediate-prelaunch and both postlaunch censuses; unchanged physical limits/no-replay.','guard267_status':'HISTORICAL_EXACT_BYTES_RECONCILED; successor absence repair independently PASSED26; original gap and reproducer retained', 'guard_review26':json.loads((J.parent/'mac-archive-memo-absence-guard-review26.json').read_text()), 'scope_boundary':'Exact selected position/integer-root/packed candidate transfer and original imported dependencies; actual field instance/concrete semantics/legal construction/native/full Transfer remain OPEN','full_transfer':'OPEN'}
(J/'import-guard-review01.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'modules':len(active_fresh),'associations':len(associations),'pins':len(checked),'prior':sum(a['prior_published']for a in associations.values()),'guards':sorted({v[1]for v in configs.values()})}))
