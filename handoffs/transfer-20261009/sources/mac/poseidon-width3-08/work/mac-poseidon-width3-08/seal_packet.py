"""Seal this finite measured instance; raw logs stay local and are hash-bound."""
import hashlib,json,subprocess,time
from pathlib import Path
STAGE=Path(__file__).resolve().parent; ROOT=STAGE.parents[1]
OUT=ROOT/'outputs/mac-poseidon-width3-08'; PROJECT=STAGE/'project'
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as stream:
  while b:=stream.read(1024**2):h.update(b)
 return h.hexdigest()
def identity(path):return dict(bytes=path.stat().st_size,sha256=sha(path))
def snapshot():
 d=json.loads((OUT/'rounds-full01.json').read_text()); provenance=ROOT/'outputs/mac-transfer-pilot01/provenance-successor01.json'
 assert sha(OUT/'rounds-full01.json')=='6d903d9380ab2e54b6e0207b5283c3786ea33a1500b7124a1d944bd3da452975'
 assert sha(provenance)==d['provenance_receipt_sha256']
 p=json.loads(provenance.read_text()); assert p['runtime_sha']==d['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
 assert p['modulus']==d['modulus']
 pinned=ROOT/'outputs/mac-row-replay/pinned-inputs.json'; assert sha(pinned)==p['runtime_manifest_sha256']
 baseline=ROOT/'work/runtime-snapshot'; runtime=ROOT/'work/parent-full-program/runtime'
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=baseline,text=True).strip()==d['runtime_sha']
 assert not subprocess.check_output(['git','status','--porcelain'],cwd=baseline,text=True).strip()
 sources=[]
 for item in p['runtime_sources']:
  a=sha(baseline/item['path']); b=sha(runtime/item['path'])
  assert a==item['baseline_sha256'] and b==item['capture_sha256'],item['path']
  sources.append(item)
 assert len(sources)==1209 and sum(i['baseline_sha256']!=i['capture_sha256'] for i in sources)==4
 inputs={name:identity(ROOT/'work/parent-full-program/capture'/name) for name in d['qualified_inputs']}
 assert inputs==d['qualified_inputs']==p['inputs']
 helpers=json.loads((ROOT/'outputs/mac-m18-framing01/input-manifest.json').read_text())['sources']
 for helper in helpers: assert sha(ROOT/'work/mac-m18-framing01'/helper['path'])==helper['sha256']
 parameter=baseline/'crates/crypto/primitives/params/poseidon381.json'
 assert sha(parameter)==d['parameter_sha256']=='f45040142a56e16bb8480f1f6648621d32f456646cfaf77beca2b05a6bb12742'
 for name,item in d['parent_inputs'].items():assert sha(ROOT/item['path'])==item['sha256']
 for path,h in d['source_guard_identities'].items():assert sha(ROOT/path)==h
 return dict(parameter_sha256=sha(parameter),runtime_sha=d['runtime_sha'],modulus=d['modulus'],inputs=inputs,
   descriptor_sha256=sha(OUT/'rounds-full01.json'),provenance_receipt_sha256=sha(provenance),
   runtime_manifest_sha256=sha(pinned),runtime_sources_digest=hashlib.sha256(json.dumps(sources,sort_keys=True).encode()).hexdigest(),
   baseline_files_checked=1209,diagnostic_overlays=p['diagnostic_overlays'],qualified_reader_sources=helpers,
   clean_source_verifier_vk_correspondence='OPEN',full_transfer='OPEN')
from audit_log import validate
started=time.monotonic();before=snapshot();packet=json.loads((OUT/'input-packet01.json').read_text())
modules=sorted(p.stem for p in (PROJECT/'ShielddSecurity').glob('*.lean') if p.stem.startswith('TransferPoseidonWidth3') or p.stem in ['PoseidonHash3OneBlock08','PoseidonCallTraversal03'])
assert len(modules)==81,len(modules)
receipts={};costs=[];imports={};official=set();attempts=[]
for name in modules:
 source=PROJECT/'ShielddSecurity'/(name+'.lean');obj=PROJECT/'.lake/build/lib/lean/ShielddSecurity'/(name+'.olean')
 matches=[]
 for rp in sorted(OUT.glob('build-'+name+'-*.json')):
  result=json.loads(rp.read_text());attempts.append(rp)
  if result['status']=='passed' and result['source_sha256']==sha(source) and result['object_sha256']==sha(obj):matches.append((rp,result))
 assert matches,'unqualified '+name
 rp,result=matches[-1];assert result['command'][-1]==str(source)
 assert result['lean_heap_limit_MiB']==2048 and '-M2048' in result['command'] and '-j1' in result['command']
 log=rp.with_suffix('.log');assert sha(log)==result['log_sha256']
 audited=validate(log.read_text(),result['expected_axiom_names'],result['expected_signature_names']);assert audited['axiom_audits']==result['axiom_audits']
 for imported,item in result['frozen_imports'].items():
  if not imported.startswith('ShielddSecurity.'):continue
  sp=PROJECT/(imported.replace('.','/')+'.lean');op=PROJECT/'.lake/build/lib/lean'/(imported.replace('.','/')+'.olean')
  assert sha(sp)==item['source_sha256'] and sha(op)==item['object_sha256'],imported
  short=imported.removeprefix('ShielddSecurity.')
  if short not in modules:
   inherited=packet['reused'][short]
   assert inherited['source_sha256']==sha(sp) and inherited['object_sha256']==sha(op)
   original=ROOT/inherited['original_receipt_path'];assert sha(original)==inherited['original_receipt_sha256']
   value=dict(**item,source_path=str(sp.relative_to(ROOT)),prior_receipt=inherited['original_receipt_path'],prior_receipt_sha256=sha(original),credit='inherited exact source/object; no fresh module execution')
   if imported in imports:assert imports[imported]==value
   imports[imported]=value
 closure=result['frozen_imports']['official_import_closure'];m=OUT/closure['manifest_file'];assert sha(m)==closure['manifest_sha256'];official.add(m)
 receipts[name]=dict(path=str(rp.relative_to(ROOT)),sha256=sha(rp),audits=result['axiom_audits'])
 costs.append(dict(module=name,source_bytes=source.stat().st_size,object_bytes=obj.stat().st_size,seconds=result['seconds'],peak_group_rss_bytes=result['peak_group_rss_bytes'],audits=result['axiom_audits'],heap_MiB=2048))
generated=[n for n in modules if (PROJECT/'ShielddSecurity'/(n+'.lean')).read_text().startswith('-- GENERATED')]
expected={name:sha(PROJECT/'ShielddSecurity'/(name+'.lean')) for name in generated}
for script in ['generate_direct.py','generate_absorption.py','generate_absorption_controls.py','generate_full_blocks.py','generate_full_block_proofs.py','generate_full_block_certificates.py','generate_full_program.py','generate_full_semantic.py','generate_full_checked.py']:
 subprocess.run(['python3',str(STAGE/script)],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
assert expected=={name:sha(PROJECT/'ShielddSecurity'/(name+'.lean')) for name in generated}
after=snapshot();assert before==after
scope='first captured width3 Poseidon full65/hash3; domain24 arity2 IV536, prior source-cut LCs16577/21951, internal state1 linear port raw23593 metadata; arbitrary same finalrho + exact321 selected-row constructor240arithmetic+onecopy; conditional Field/CharP/one/four/prior-copy. Upstream cuts/full-parent inclusion/native runtime OPEN.'
(OUT/'seal-provenance01.json').write_text(json.dumps(dict(status='passed',before=before,after_equal_before=True,generated_sources_equal=True,generated_source_count=len(generated),inherited_imports=imports,scope=scope,seconds=time.monotonic()-started),indent=2)+'\n')
failures=[]
for rp in sorted(set(attempts)):
 d=json.loads(rp.read_text())
 if d['status']!='passed':failures.append(dict(receipt=str(rp.relative_to(ROOT)),source_sha256=d['source_sha256'],status=d['status'],exit=d.get('exit'),reason=d.get('reason'),heap_MiB=d['lean_heap_limit_MiB'],proof_credit=0))
floor=next(x for x in costs if 'ImportFloor' in x['module']);full=[x for x in costs if 'Call08' in x['module'] and 'ImportFloor' not in x['module']];core=[x for x in costs if 'Controls' not in x['module'] and 'ImportFloor' not in x['module']]
summary=dict(schema='bounded-width3-full65-result-v1',status='passed',scope=scope,runtime_sha=before['runtime_sha'],fresh_modules=len(modules),fresh_fulltype_and_axiom_audits=sum(x['audits'] for x in costs),inherited_module_executions=0,
 accounting=dict(raw_nodes=1600,allocated_constants=973,selected_original_row_indices=list(range(1986,2306))+[200769],rows=321,materialized_steps=240,copy_steps=1,rounds=65,boundaries=64,source_cut_refs=[16577,21951],domain=24,arity=2,IV=536,result_source_node_metadata=23593,result_state_column=1,fresh_columns=[24724,25043],maximum_precanonical_MDS_terms=121),
 module_costs=costs,core_source_bytes=sum(x['source_bytes'] for x in core),core_object_bytes=sum(x['object_bytes'] for x in core),core_seconds=sum(x['seconds'] for x in core),full_family_source_bytes=sum(x['source_bytes'] for x in full),full_family_object_bytes=sum(x['object_bytes'] for x in full),full_family_seconds=sum(x['seconds'] for x in full),import_floor=floor,peak_group_RSS_bytes=max(x['peak_group_rss_bytes'] for x in costs),RSS_minus_import_floor={x['module']:x['peak_group_rss_bytes']-floor['peak_group_rss_bytes'] for x in costs},RSS_note='sampled total group RSS; difference from same-import floor is observational, not heap/cache diagnosis',
 controls=dict(absorption_matcher_rejections=9,full_traversal_guard_rejections=3,positive_controls=True,semantic_inequality_claim=False,failed_modules_credit=0),failures=failures,
 limits=dict(LEAN_NUM_THREADS=1,j=1,heap_MiB=2048,seconds_per_module=240,group_RSS_bytes=4*1024**3,admission_free_memory_percent=15,free_disk_bytes=2*1024**3),
 open=['upstream cut evaluation/native identity','exact full captured-parent row inclusion/partition','runtime callsite/consumer attribution','clean-source verifier/VK correspondence','whole Transfer theorem'],full_scale_claim=False,full_transfer='OPEN')
(OUT/'full-call-result01.json').write_text(json.dumps(summary,indent=2)+'\n')
files=[]
def add(path,category,publish=True):
 if any(x['path']==str(path.relative_to(ROOT)) for x in files):return
 files.append(dict(path=str(path.relative_to(ROOT)),category=category,publication=publish,**identity(path)))
for path in sorted(STAGE.glob('*.py')):add(path,'handwritten_generator_or_guard')
for path in sorted(STAGE.glob('*.lean.txt')):add(path,'maintained_proof_or_control_template')
for name in modules:add(PROJECT/'ShielddSecurity'/(name+'.lean'),'generated_instance' if name in generated else 'handwritten_helper_or_verification_floor')
for name in ['lakefile.lean','lake-manifest.json','lean-toolchain']:add(PROJECT/name,'package_identity')
for name in ['parent-descriptor.json','parent-match.py','CHECKPOINT.md','checkpoint01.json']:add(STAGE/name,'frozen_parent_input_or_historical_checkpoint')
for rp in sorted(set(attempts)):add(rp,'fresh_pass_or_failure_receipt');add(rp.with_suffix('.log'),'raw_observation_local_only',False)
for m in sorted(official):add(m,'deduplicated_official_import_closure')
for rp in sorted(OUT.glob('*.json')):
 if rp.name.startswith(('publication-','build-','seal-guard','official-imports')):continue
 local=rp.name in ['rounds-full01.json','rounds01.json']
 add(rp,'descriptor_local_only' if local else 'qualified_data_or_provenance_or_generation_metadata',not local)
for rp in sorted(OUT.glob('*.log')):
 if not rp.name.startswith('seal-guard'):add(rp,'raw_observation_local_only',False)
for rp in sorted(OUT.glob('seal-guard*.json')):
 add(rp,'prior_completed_seal_guard_receipt');add(rp.with_suffix('.log'),'prior_completed_seal_guard_observation_local_only',False)
for rp in sorted(OUT.glob('publication-manifest*.json')):add(rp,'preserved_predecessor_metadata_failure_zero_credit')
for rp in sorted((OUT/'source-history').glob('*')):
 if rp.is_file():add(rp,'preserved_source_predecessor_zero_credit')
manifest=dict(schema='width3-full65-publication-v1',runtime_sha=before['runtime_sha'],files=files,current_pass_receipts=receipts,inherited_imports=imports,source_objects_not_published=True,raw_descriptors_and_logs_local_only=True,post_run_envelope_required=True,full_transfer='OPEN')
attempt=1
while (OUT/f'publication-manifest{attempt:02d}.json').exists():attempt+=1
p=OUT/f'publication-manifest{attempt:02d}.json';p.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(status='passed',manifest_sha256=sha(p),files=len(files),publication_files=sum(x['publication'] for x in files),fresh_modules=len(modules),audits=summary['fresh_fulltype_and_axiom_audits'],seconds=time.monotonic()-started)),flush=True)
