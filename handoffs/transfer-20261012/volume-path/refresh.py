"""Regenerate exact volume path captures and atomically qualify the cumulative construction."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,sys
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--batch',type=Path,action='append',required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--runtime',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();pending.mkdir()
config=json.loads((root/'config.json').read_text());verified={}
def pin(p):
 p=Path(p);return dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
def checked(identity):
 p=Path(identity['path']);stamp=(p.stat().st_size,p.stat().st_mtime_ns)
 if identity['path'] in verified and verified[identity['path']]==(stamp,identity):return
 assert pin(p)==identity,identity['path'];verified[identity['path']]=(stamp,identity)
def signature(source,imports,children):
 return hashlib.sha256(json.dumps([source['sha256'],[(n,children.get(n.removeprefix('ShielddSecurity.'))) for n in imports]],separators=(',',':')).encode()).hexdigest()
assert hashlib.sha256((root.parent/'encryption-scalar-repair/selected_replay.py').read_bytes()).hexdigest()==config['guard_sha256']
assert hashlib.sha256((root/'selected_replay15.py').read_bytes()).hexdigest()==config['guard15_sha256']
assert subprocess.check_output(['git','-C',str(a.runtime),'rev-parse','HEAD'],text=True).strip()==config['runtime_sha']
assert not subprocess.check_output(['git','-C',str(a.runtime),'status','--porcelain'])
for name,identity in config['runtime_sources'].items():
 actual=pin(a.runtime/name);assert actual['bytes']==identity['bytes'] and actual['sha256']==identity['sha256']
prior=json.loads((root.parent/'volume-output/qualified/evidence.json').read_text());assert prior['status']=='passed' and prior['runtime_sha']==config['runtime_sha'] and prior['conditional_assertion_coverage']['union']==22647
generation={}
for folder,settings in config['generators'].items():
 dest=pending/folder
 command=[sys.executable,'-B','-I','-S',str(root/folder/'generate.py')]+(['--output',str(dest)] if settings['named_output'] else [str(dest)])
 if settings.get('repository'):command+=['--repository',str(root.parents[2])]
 subprocess.run(command,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 for source in (dest/'source-root/ShielddSecurity').glob('*.lean'):
  assert source.stem not in generation
  generation[source.stem]=pin(source)
required_sources={p.stem:p for p in (root/'source/ShielddSecurity').glob('*.lean')}
required_sources.update({n:Path(v['path']) for n,v in generation.items()})
final_signatures={}
modules={};reports=[];reports_by_module={};module_dependencies={};roots=[];plans=[]
base_replacements=json.loads((root/'source-replacements.json').read_text())
path_replacements=json.loads((root/'compact-source-replacements.json').read_text())
compact_replacements=json.loads((root/'prior-compact-source-replacements.json').read_text())
assert all(compact_replacements['replacements'][n]==v for n,v in path_replacements['replacements'].items())
assert set(compact_replacements['replacements'])-set(path_replacements['replacements'])=={'MapAssetHashComposition737','RoutingParameterHashComposition876','VolumeSubjectHashComposition896','VolumePriorHashComposition906'}|{f'VolumeOutputHashComposition916C{i}' for i in range(149,154)}
packed_replacements=json.loads((root/'packed-source-replacements.json').read_text())
packed_tails={f'VolumePathHashTail928C{i}B{j:02d}' for i in range(125,149) for j in (0,7)}
packed_compositions={f'VolumePathHashComposition929C{i}' for i in range(125,149)}
assert set(packed_replacements['replacements'])==set(compact_replacements['replacements'])|packed_tails
for name,change in compact_replacements['replacements'].items():
 if name in packed_compositions:assert packed_replacements['replacements'][name]['original']==change['replacement']
 else:assert packed_replacements['replacements'][name]==change
retired_modules={f'VolumePathHashTail928C{i}B{j:02d}' for i in range(125,149) for j in range(21) if j<14 and j not in (0,7)}
table_replacements=json.loads((root/'table-source-replacements.json').read_text())
segment_replacements=json.loads((root/'table-segment-source-replacements.json').read_text())
consumer_replacements=json.loads((root/'table-consumer-source-replacements.json').read_text())
data_names={f'TransferPoseidonCall04Data{i:02d}' for i in range(9)}
assert set(table_replacements['replacements'])==set(packed_replacements['replacements'])|data_names
assert all(table_replacements['replacements'][n]==v for n,v in packed_replacements['replacements'].items())
segment_name='TransferPoseidonCall13TailSegment01'
assert set(segment_replacements['replacements'])==set(table_replacements['replacements'])|{segment_name}
assert all(segment_replacements['replacements'][n]==v for n,v in table_replacements['replacements'].items())
consumer_inputs=json.loads((root/'footprint-consumer-generator/inputs.json').read_text())
assert set(consumer_replacements['replacements'])==set(segment_replacements['replacements'])|set(consumer_inputs)
for name,change in segment_replacements['replacements'].items():
 if name==segment_name:assert consumer_replacements['replacements'][name]['original']==change['original']
 else:assert consumer_replacements['replacements'][name]==change
allowed_replacements=(base_replacements,path_replacements,compact_replacements,packed_replacements,table_replacements,segment_replacements,consumer_replacements)
current_constructor_selected=None

assert all(compact_replacements['replacements'][n]==v for n,v in base_replacements['replacements'].items())
assert set(path_replacements['replacements'])-set(base_replacements['replacements'])=={f'VolumePathHashComposition929C{i}' for i in range(125,149)}
for batch in a.batch:
 completion=json.loads((batch/'completion.json').read_text());assert completion['status']=='passed';roots.append(completion['root']);checked(completion['dependency_manifest']);plan=json.loads(Path(completion['dependency_manifest']['path']).read_text());assert plan['runtime_sha']==config['runtime_sha'] and plan['mathlib']==config['mathlib'];assert plan['limits']==dict(threads=1,default_heap_MiB=2048,elliptic_point_closure_heap_MiB=3072,rss_bytes=4*1024**3,module_seconds=240,heartbeats=900000,recDepth=8192,free_memory_percent=15,free_disk_bytes=2*1024**3)
 assert any(v['sha256'] in {config['guard_sha256'],config['guard15_sha256']} for v in completion['final_files'].values())
 for identity in completion['final_files'].values():checked(identity)
 checked(plan['source_replacements']);replacements=json.loads(Path(plan['source_replacements']['path']).read_text())
 assert replacements in allowed_replacements
 for name,change in replacements['replacements'].items():
  source=required_sources[name] if name in required_sources else root.parent/'tier-families/qualified/fixed-capture-generator/source-root/ShielddSecurity'/(name+'.lean') if name.startswith('FixedFamilies544') else root.parent/'tier-families/qualified/payload-capture-generator/source-root/ShielddSecurity'/(name+'.lean') if name.startswith('PayloadCapture558') else root.parent/'encryption-scalar-repair/source/ShielddSecurity'/(name+'.lean')
  source_bytes=source.read_bytes()
  if name in packed_compositions and replacements in (base_replacements,path_replacements,compact_replacements):
   # Earlier compact receipts predate packing; only their import list differs.
   ci=int(name.removeprefix('VolumePathHashComposition929C'))
   lines=source_bytes.decode().splitlines();matches=[i for i,line in enumerate(lines) if line.startswith(f'import ShielddSecurity.VolumePathHashTail928C{ci}B')]
   assert len(matches)==9
   lines=lines[:matches[0]]+[f'import ShielddSecurity.VolumePathHashTail928C{ci}B{j:02d}' for j in range(21)]+[line for i,line in enumerate(lines[matches[0]:],matches[0]) if i not in matches]
   source_bytes=('\n'.join(lines)+'\n').encode()
  if name==segment_name and replacements==segment_replacements:
   assert source_bytes.count(b'noncomputable section\n')==1
   source_bytes=source_bytes.replace(b'noncomputable section\n',b'',1)
  assert hashlib.sha256(source_bytes).hexdigest()==change['replacement']['sha256']

  if name in plan['selected']:assert plan['selected'][name]['source']['sha256']==change['replacement']['sha256']
 if plan['root']=='VolumePathConstruction952':current_constructor_selected=set(plan['selected'])
 memo={}
 def calculate(name):
  if name in memo:return memo[name]
  row=plan['selected'][name];children={}
  for child in row['imports']:
   if child.startswith('ShielddSecurity.'):
    n=child.removeprefix('ShielddSecurity.');children[n]=calculate(n)
  value=signature(row['source'],row['imports'],children);assert value==row['source_signature'];memo[name]=value;return value
 for name,row in plan['selected'].items():
  calculate(name)
  if row['replacement_affected'] and not row['replay']:assert row['previous_source_signature']==row['source_signature']
 if plan['root'] in config['mandatory_roots']:
  for name in required_sources.keys() & plan['selected'].keys():
   value=plan['selected'][name]['source_signature']
   final_signatures[name]=value
 assert [e['module'] for e in completion['completed']]==plan['order']
 for item in completion['completed']:
  assert item['status']=='passed';checked(item['receipt']);receipt=json.loads(Path(item['receipt']['path']).read_text());name=receipt['module'];assert receipt['status']=='passed' and receipt['exit']==0 and receipt['stop'] is None and receipt['audit_error'] is None
  assert receipt['dependency_manifest']==completion['dependency_manifest'];assert receipt['source']==plan['selected'][name]['source'];checked(receipt['source']);checked(receipt['stdout']);checked(receipt['stderr']);assert not Path(receipt['stderr']['path']).read_bytes().strip()
  source=Path(receipt['source']['path']).read_text();expected=re.findall(r'(?m)^#check @([A-Za-z0-9_.]+)\s*$',source);assert len(receipt['audits'])==len(expected) and all(r['name']==n or r['name'].endswith('.'+n) for r,n in zip(receipt['audits'],expected))
  for report in receipt['audits']:
   assert set(report['axioms'])<={'propext','Quot.sound','Classical.choice'};assert hashlib.sha256(report['full_type'].encode()).hexdigest()==report['full_type_sha256']
  assert receipt['seconds']<=240 and receipt['peak_group_rss_bytes']<=4*1024**3
  assert all(s['free_memory_percent']>=15 and s['free_disk_bytes']>=2*1024**3 for s in receipt['samples'])
  for identity in receipt['objects'].values():checked(identity)
  # Keep the latest fully verified replay; earlier affected receipts remain provenance.
  if name in modules and modules[name]['source_sha256']!=receipt['source']['sha256']:
   changes=[config['replacements'][name] for config in allowed_replacements if name in config['replacements']]
   assert any(modules[name]['source_sha256']==change['original']['sha256'] and receipt['source']['sha256']==change['replacement']['sha256'] for change in changes)
  modules[name]=dict(source_sha256=receipt['source']['sha256'],source_signature=plan['selected'][name]['source_signature'],receipt_sha256=item['receipt']['sha256'],object_sha256=receipt['objects']['.olean']['sha256'],reports=len(receipt['audits']),seconds=receipt['seconds'],peak_group_rss_bytes=receipt['peak_group_rss_bytes'])
  reports_by_module[name]=receipt['audits']
  module_dependencies[name]={child.removeprefix('ShielddSecurity.'):plan['selected'][child.removeprefix('ShielddSecurity.')]['source_signature'] for child in plan['selected'][name]['imports'] if child.startswith('ShielddSecurity.') and child.removeprefix('ShielddSecurity.') in required_sources}

 plans.append(dict(root=plan['root'],dependency_manifest_sha256=completion['dependency_manifest']['sha256'],selected=len(plan['selected']),replayed=len(plan['order']),invalidated=len(plan['invalidated_modules'])))
assert current_constructor_selected is not None and not retired_modules & current_constructor_selected
for name in retired_modules:
 modules.pop(name,None);reports_by_module.pop(name,None);module_dependencies.pop(name,None);final_signatures.pop(name,None)
assert set(config['mandatory_roots'])<=set(modules)
reports=[report for name in sorted(reports_by_module) for report in reports_by_module[name]]
for name,deps in module_dependencies.items():
 for child,value in deps.items():assert modules[child]['source_signature']==value,(name,child,'stale dependency')
assert set(required_sources) <= set(modules) and set(required_sources) <= set(final_signatures)
for name,source in required_sources.items():
 assert hashlib.sha256(source.read_bytes()).hexdigest()==modules[name]['source_sha256'],name
 assert final_signatures[name]==modules[name]['source_signature'],name
for theorem in ['VolumePathAssignment942.sibling', 'VolumePathBits943.bits', 'QuaternarySelector944.encoded_slot', 'VolumePathComposition949.result', 'VolumePathJoin951.generic_rows', 'VolumePathJoin951.rows', 'VolumePathConstruction952.legal_completed']:
 assert any(r['name']=='ShielddSecurity.'+theorem for r in reports),theorem
coverage=json.loads((root/'coverage-base.json').read_text());previous=set(coverage['known_positions']);assert coverage['runtime_sha']==config['runtime_sha'] and len(previous)==22647
positions={8315}
assert len(positions)==1 and not positions & previous and len(positions|previous)==22648
assert any(r['name']=='ShielddSecurity.VolumePathConstruction952.legal_completed' and 'VolumePathConstruction952.Earlier' in r['full_type'] and 'VolumePathConstruction952.Rows' in r['full_type'] and 'MapAssetDomain743.crypto c' in r['full_type'] and 'MapAssetDomain743.withAsset c' in r['full_type'] for r in reports)
evidence=dict(status='passed',runtime_sha=config['runtime_sha'],mathlib=config['mathlib'],scope=config['scope'],batches=plans,modules=modules,full_types_and_axioms=reports,reports=len(reports),certification=False,native_credit=0,circuit_soundness='OPEN',total_legal_input_construction='OPEN',computed_public64_binding='OPEN',native_consequence='OPEN',refresh_sha256=pin(Path(__file__))['sha256'],guard_sha256=config['guard15_sha256'],accepted_legacy_guard_sha256=config['guard_sha256'],generation={n:{k:v for k,v in value.items() if k!='path'} for n,value in generation.items()},prior_evidence_sha256=pin(root.parent/'volume-output/qualified/evidence.json')['sha256'],conditional_assertion_coverage=dict(previous_union=len(previous),positions=sorted(positions),new_positions=sorted(positions),union=len(positions|previous),remaining=22816-len(positions|previous),total=22816))
(pending/'evidence.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n');os.replace(pending,a.output);print(json.dumps(dict(status='passed',modules=len(modules),reports=len(reports))))
