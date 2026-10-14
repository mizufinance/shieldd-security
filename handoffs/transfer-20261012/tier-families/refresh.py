"""Reproduce and atomically qualify five retained tier multiplication families."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,sys
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--batch',type=Path,action='append',required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();assert not a.output.exists();pending=a.output.with_name(a.output.name+'.pending');assert not pending.exists();pending.mkdir()
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
prior=json.loads((root.parent/'ownership-families/qualified/evidence.json').read_text());assert prior['status']=='passed' and prior['runtime_sha']==config['runtime_sha'] and prior['conditional_assertion_coverage']['union']==17979
generation={}
for folder,settings in config['generators'].items():
 dest=pending/folder
 command=[sys.executable,'-B','-I','-S',str(root/folder/'generate.py')]+(['--output',str(dest)] if settings['named_output'] else [str(dest)])
 subprocess.run(command,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 for source in (dest/'source-root/ShielddSecurity').glob('*.lean'):
  assert source.stem not in generation
  generation[source.stem]=pin(source)
required_sources={p.stem:p for p in (root/'source/ShielddSecurity').glob('*.lean')}
required_sources.update({n:Path(v['path']) for n,v in generation.items()})
final_signatures={}
modules={};reports=[];roots=[];plans=[]
for batch in a.batch:
 completion=json.loads((batch/'completion.json').read_text());assert completion['status']=='passed';roots.append(completion['root']);checked(completion['dependency_manifest']);plan=json.loads(Path(completion['dependency_manifest']['path']).read_text());assert plan['runtime_sha']==config['runtime_sha'] and plan['mathlib']==config['mathlib'];assert plan['limits']==dict(threads=1,default_heap_MiB=2048,elliptic_point_closure_heap_MiB=3072,rss_bytes=4*1024**3,module_seconds=240,heartbeats=900000,recDepth=8192,free_memory_percent=15,free_disk_bytes=2*1024**3)
 assert any(v['sha256']==config['guard_sha256'] for v in completion['final_files'].values())
 for identity in completion['final_files'].values():checked(identity)
 checked(plan['source_replacements']);replacements=json.loads(Path(plan['source_replacements']['path']).read_text())
 expected_replacements=json.loads((root/'source-replacements.json').read_text())
 if replacements!=expected_replacements:
  assert replacements in [json.loads((root/name).read_text()) for name in ['source-replacements-base.json','source-replacements-payload.json']]
  assert not (set(expected_replacements['replacements'])-set(replacements['replacements'])) & set(plan['selected'])
 for name,change in replacements['replacements'].items():
  source=Path(generation[name]['path']) if name.startswith(('PayloadCapture558','FixedFamilies544')) else root.parent/'encryption-scalar-repair/source/ShielddSecurity'/(name+'.lean');assert hashlib.sha256(source.read_bytes()).hexdigest()==change['replacement']['sha256']
  if name in plan['selected']:assert plan['selected'][name]['source']['sha256']==change['replacement']['sha256']
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
 if plan['root'] in ['TierConstruction636','TierFinal637']:
  for name in required_sources.keys() & plan['selected'].keys():
   value=plan['selected'][name]['source_signature']
   if name in final_signatures:assert final_signatures[name]==value,name
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
  if name in modules:assert modules[name]['source_sha256']==receipt['source']['sha256']
  else:
   modules[name]=dict(source_sha256=receipt['source']['sha256'],source_signature=plan['selected'][name]['source_signature'],receipt_sha256=item['receipt']['sha256'],object_sha256=receipt['objects']['.olean']['sha256'],reports=len(receipt['audits']),seconds=receipt['seconds'],peak_group_rss_bytes=receipt['peak_group_rss_bytes']);reports+=receipt['audits']
 plans.append(dict(root=plan['root'],dependency_manifest_sha256=completion['dependency_manifest']['sha256'],selected=len(plan['selected']),replayed=len(plan['order']),invalidated=len(plan['invalidated_modules'])))
assert set(config['mandatory_roots'])<=set(roots)
assert set(required_sources) <= set(modules) and set(required_sources) <= set(final_signatures)
for name,source in required_sources.items():
 assert hashlib.sha256(source.read_bytes()).hexdigest()==modules[name]['source_sha256'],name
 assert final_signatures[name]==modules[name]['source_signature'],name
for theorem in ['TierConstruction636.legal_completed','TierFinal637.final_point']:
 assert any(r['name']=='ShielddSecurity.'+theorem for r in reports),theorem
old_payload=json.loads((root.parent/'payload-families/qualified/evidence.json').read_text())
old_audits={r['name']:r for r in old_payload['full_types_and_axioms'] if r['name'].startswith('ShielddSecurity.PayloadCapture558')}
new_audits={r['name']:r for r in reports if r['name'].startswith('ShielddSecurity.PayloadCapture558')}
assert len(old_audits)==568 and set(old_audits)==set(new_audits)
for name,report in new_audits.items():
 assert report['full_type']==old_audits[name]['full_type'] and set(report['axioms'])==set(old_audits[name]['axioms']),name
old_fixed=json.loads((root.parent/'fixed-families/qualified/evidence.json').read_text())
old_fixed_first=json.loads((root.parent/'fixed-family-first/qualified/evidence.json').read_text())
old_fixed_audits={r['name']:r for evidence in [old_fixed_first,old_fixed] for r in evidence['full_types_and_axioms'] if r['name'].startswith('ShielddSecurity.FixedFamilies544')}
new_fixed_audits={r['name']:r for r in reports if r['name'].startswith('ShielddSecurity.FixedFamilies544')}
assert len(old_fixed_audits)==5536 and set(old_fixed_audits)==set(new_fixed_audits)
for name,report in new_fixed_audits.items():
 assert report['full_type']==old_fixed_audits[name]['full_type'] and set(report['axioms'])==set(old_fixed_audits[name]['axioms']),name
coverage=json.loads((root/'coverage-base.json').read_text());previous=set(coverage['known_positions']);assert coverage['runtime_sha']==config['runtime_sha'] and len(previous)==17979
families=json.loads((root/'capture-generator/families.json').read_text());assert [f['assertions'] for f in families]==[11909,12665,13931,15197,16463]
positions={p for f in families for p in range(f['assertions'],f['assertions']+756)}
assert len(positions)==3780 and not positions & previous and len(positions|previous)==21759
evidence=dict(status='passed',runtime_sha=config['runtime_sha'],mathlib=config['mathlib'],scope='Five selected-key tier multiplication families on one retained legal-input assignment, with explicit semantic flag seeding and preservation, exact detection and payload selectors, captured operations, initial rows, canonical scalar bits and final point meanings. Full Transfer endpoints remain open.',batches=plans,modules=modules,full_types_and_axioms=reports,reports=len(reports),certification=False,native_credit=0,circuit_soundness='OPEN',total_legal_input_construction='OPEN',computed_public64_binding='OPEN',native_consequence='OPEN',refresh_sha256=pin(Path(__file__))['sha256'],guard_sha256=config['guard_sha256'],generation={n:{k:v for k,v in value.items() if k!='path'} for n,value in generation.items()},prior_evidence_sha256=pin(root.parent/'ownership-families/qualified/evidence.json')['sha256'],conditional_assertion_coverage=dict(previous_union=len(previous),positions=sorted(positions),new_positions=sorted(positions),union=len(positions|previous),remaining=22816-len(positions|previous),total=22816))
(pending/'evidence.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n');os.replace(pending,a.output);print(json.dumps(dict(status='passed',modules=len(modules),reports=len(reports))))
