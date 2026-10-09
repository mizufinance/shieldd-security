"""Seal this finite measured instance; raw logs stay local and are hash-bound."""
import hashlib,json,subprocess,time
from pathlib import Path
STAGE=Path(__file__).resolve().parent; ROOT=STAGE.parents[1]
OUT=ROOT/'outputs/mac-poseidon-rename05'; PROJECT=STAGE/'project'
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as stream:
  while b:=stream.read(1024**2):h.update(b)
 return h.hexdigest()
def identity(path):return dict(bytes=path.stat().st_size,sha256=sha(path))
def snapshot():
 d=json.loads((OUT/'second-tail02.json').read_text()); provenance=ROOT/'outputs/mac-transfer-pilot01/provenance-successor01.json'
 assert sha(OUT/'second-tail02.json')=='7e7e686ff3572d5be3f0cd4e405124863147230f64e1c620f536282067e3c57b'
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
 assert sha(ROOT/'outputs/mac-m18-framing01/input-manifest.json')==d['qualified_reader_manifest_sha256']
 assert helpers==d['qualified_reader_sources']
 for helper in helpers: assert sha(ROOT/'work/mac-m18-framing01'/helper['path'])==helper['sha256']
 parameter=baseline/'crates/crypto/primitives/params/poseidon381-wide.json'
 assert sha(parameter)=='84a51d11b64641fc3604b4cbedbe7cc82e91204b21d3bd62fb59462bbb4a5bb8'
 for path,h in d['source_guards'].items():assert sha(ROOT/path)==h
 return dict(parameter_sha256=sha(parameter),runtime_sha=d['runtime_sha'],modulus=d['modulus'],inputs=inputs,
   descriptor_sha256=sha(OUT/'second-tail02.json'),provenance_receipt_sha256=sha(provenance),
   runtime_manifest_sha256=sha(pinned),runtime_sources_digest=hashlib.sha256(json.dumps(sources,sort_keys=True).encode()).hexdigest(),
   baseline_files_checked=1209,diagnostic_overlays=p['diagnostic_overlays'],qualified_reader_sources=helpers,
   clean_source_verifier_vk_correspondence='OPEN',full_transfer='OPEN')
from audit_log import validate
started=time.monotonic();before=snapshot()
inherited=json.loads((OUT/'inherited-sealed01.json').read_text())
for item in [dict(path=inherited['manifest_path'],sha256=inherited['manifest_sha256'])]+inherited.get('prior_manifests',[]):assert sha(ROOT/item['path'])==item['sha256']
modules=sorted(p.stem for p in (PROJECT/'ShielddSecurity').glob('*.lean') if p.stem.startswith(('TransferPoseidonSecondTail05','TransferPoseidonTailTemplate05','CompilerColumnRenaming05','CompilerWindowRenaming05','CompilerRenamingChecks05','PoseidonRoundSuffix05')))
handwritten=[n for n in modules if n.startswith(('Compiler','PoseidonRoundSuffix')) or 'ImportFloor' in n]
generated=[n for n in modules if n not in handwritten]
receipts={};costs=[];inherited_imports={};fresh_receipt_paths=[];official_manifests=set()
for name in modules:
 source=PROJECT/'ShielddSecurity'/(name+'.lean');obj=PROJECT/'.lake/build/lib/lean/ShielddSecurity'/(name+'.olean')
 matching=[]
 for path in sorted(OUT.glob('build-'+name+'-*.json')):
  result=json.loads(path.read_text())
  if result['status']=='passed' and result['source_sha256']==sha(source) and result['object_sha256']==sha(obj):matching.append((path,result))
 assert matching,'unqualified source/object '+name
 path,result=matching[-1];assert result['command'][-1]==str(source)
 assert result['lean_heap_limit_MiB']==2048 and '-M2048' in result['command'] and '-j1' in result['command']
 log=path.with_suffix('.log');assert sha(log)==result['log_sha256']
 audited=validate(log.read_text(),result['expected_axiom_names'],result['expected_signature_names']);assert audited['axiom_audits']==result['axiom_audits']
 for imported,item in result['frozen_imports'].items():
  if not imported.startswith('ShielddSecurity.'):continue
  sourcePath=PROJECT/(imported.replace('.','/')+'.lean');objectPath=PROJECT/'.lake/build/lib/lean'/(imported.replace('.','/')+'.olean')
  assert sha(sourcePath)==item['source_sha256'] and sha(objectPath)==item['object_sha256'],imported
  short=imported.removeprefix('ShielddSecurity.')
  if short not in modules:
   candidates=[]
   for directory in ['mac-poseidon-round01','mac-poseidon-absorb02','mac-poseidon-late03','mac-poseidon-call04']:
    for rp in sorted((ROOT/'outputs'/directory).glob('build-'+short+'-*.json')):
     r=json.loads(rp.read_text())
     if r['status']=='passed' and r['source_sha256']==item['source_sha256'] and r['object_sha256']==item['object_sha256']:candidates.append(rp)
   assert candidates,'unqualified inherited source '+imported
   rp=sorted(candidates)[-1];value=dict(**item,source_path=str(sourcePath.relative_to(ROOT)),prior_receipt=str(rp.relative_to(ROOT)),prior_receipt_sha256=sha(rp),credit='inherited sealed proof, not fresh replay')
   if imported in inherited_imports:assert inherited_imports[imported]==value
   inherited_imports[imported]=value
 official=result['frozen_imports']['official_import_closure'];assert sha(OUT/official['manifest_file'])==official['manifest_sha256'];official_manifests.add(OUT/official['manifest_file'])
 receipts[name]=dict(path=str(path.relative_to(ROOT)),sha256=sha(path),audits=result['axiom_audits'])
 costs.append(dict(module=name,source_bytes=source.stat().st_size,object_bytes=obj.stat().st_size,seconds=result['seconds'],peak_group_rss_bytes=result['peak_group_rss_bytes'],audits=result['axiom_audits'],heap_MiB=result['lean_heap_limit_MiB']))
 fresh_receipt_paths.extend(OUT.glob('build-'+name+'-*.json'))
expected={name:sha(PROJECT/'ShielddSecurity'/(name+'.lean')) for name in generated}
for script in ['generate_tail_template.py','generate_tail_semantic.py','generate_second_data.py','generate_row_checks.py','generate_port_checks.py','generate_second_proof.py','generate_controls.py']:
 subprocess.run(['python3',str(STAGE/script)],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
assert expected=={name:sha(PROJECT/'ShielddSecurity'/(name+'.lean')) for name in generated}
after=snapshot();assert before==after
scope='second captured width6 rounds2..64 tail, injective fresh-window swap+416, SAME final rho native roundsFrom2 length63, original373 rows and279 materialized+copy, arbitrary prior cutLC extension; original input/header/copy and all outside write interval preserved; no round0/1 absorption or parent/native call identity'
(OUT/'seal-provenance01.json').write_text(json.dumps(dict(status='passed',before=before,after_equal_before=True,generated_sources_equal=True,generated_source_count=len(generated),inherited_packet=inherited,inherited_imports=inherited_imports,scope=scope,seconds=time.monotonic()-started),indent=2)+'\n')
# Compact replay also reproduces all11 actual target data modules without loading the full local descriptor.
compact=OUT/'consumer-input01.json'
subprocess.run(['python3',str(STAGE/'generate_second_data.py'),'--consumer',str(compact),sha(compact)],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
assert expected=={name:sha(PROJECT/'ShielddSecurity'/(name+'.lean')) for name in generated}
failures=[]
for path in sorted(set(fresh_receipt_paths)):
 r=json.loads(path.read_text())
 if r['status']!='passed':failures.append(dict(receipt=str(path.relative_to(ROOT)),source_sha256=r['source_sha256'],status=r['status'],exit=r.get('exit'),reason=r.get('reason'),heap_MiB=r['lean_heap_limit_MiB'],proof_credit=0))
floors={x['module']:x for x in costs if 'ImportFloor' in x['module']};floor=floors['TransferPoseidonSecondTail05ImportFloor01'];core=[x for x in costs if 'Controls' not in x['module'] and 'ImportFloor' not in x['module']];target=[x for x in core if x['module'].startswith('TransferPoseidonSecondTail05')]
summary=dict(schema='bounded-poseidon-second-tail-v1',status='passed',runtime_sha=before['runtime_sha'],fresh_modules=len(modules),fresh_audits=sum(x['audits'] for x in costs),inherited_proof_replay=False,scope=scope,
 accounting=dict(rounds=[2,64],arithmetic_raw_nodes=5193,allocated_constants=3024,original_rows=list(range(778,1150))+[200769],materialized_steps=279,shared_copy_step=1,original_rows_count=373,source_span=[6047,11239],source_column_translation=416,permutation_window=dict(start=23060,width=412,offset=416),target_write_interval=[23516,23888]),
 certificates=dict(injective_renaming=True,eval_and_rows_transport=True,Step_run_and_whole_run_commute=True,exact_actual_raw_rows_equal_renamed_template=True,exact_initial_and_final_internal_ports=True,all63_rounds_same_rho_native_suffix=True,constructive_assignment_all373_original_rows=True,all22735_source_inputs_and_columns0_1_2_preserved=True,copy_preserved=True,prior_copy_link_explicit=True,cutLC_values_preserved=True,all_columns_outside_target_write_interval_preserved=True,generic_prior_row_frame_support_interface=True,actual_global_parent_row_frame_kernel=False,round0_round1_absorption=False),
 controls=dict(same_production_checker_false=['first raw row coefficient+1','first raw row column+1','wrong translation415','copy200692→200693','non-equivalent existing finalport0 vs1'],guard=['omit first row'],mutation_ran_checked=True,type_errors_and_timeouts_credit=0),
 module_costs=costs,core_source_bytes=sum(x['source_bytes'] for x in core),core_object_bytes=sum(x['object_bytes'] for x in core),core_build_seconds=sum(x['seconds'] for x in core),target_source_bytes=sum(x['source_bytes'] for x in target),target_object_bytes=sum(x['object_bytes'] for x in target),target_build_seconds=sum(x['seconds'] for x in target),all_source_bytes=sum(x['source_bytes'] for x in costs),all_object_bytes=sum(x['object_bytes'] for x in costs),all_build_seconds=sum(x['seconds'] for x in costs),import_floors=floors,
 RSS_minus_full_import_floor={x['module']:x['peak_group_rss_bytes']-floor['peak_group_rss_bytes'] for x in costs},RSS_note='sampled total group RSS and observed differences, no inference about underlying cache/heap cause',failures=failures,failure_proof_credit=0,limits=dict(lean_threads=1,heap_MiB=2048,rss_bytes=4*1024**3,seconds_per_module=240),
 compact_input=dict(path=str(compact.relative_to(ROOT)),sha256=sha(compact),bytes=compact.stat().st_size,generated_data_modules_equal=True),
 open=['round0/1 absorption and actual hash-call grouping','runtime call identity/native header/model/field join','exact parent relation inclusion and actual whole-parent frame proof','all-transfer native/header/state composition','clean-source verifier/VK correspondence','full Transfer theorem'],full_scale_claim=False,full_transfer='OPEN')
(OUT/'second-tail-result01.json').write_text(json.dumps(summary,indent=2)+'\n')
files=[]
def add(path,category,publish=True):
 if any(x['path']==str(path.relative_to(ROOT)) for x in files):return
 files.append(dict(path=str(path.relative_to(ROOT)),category=category,publication=publish,**identity(path)))
for path in sorted(STAGE.glob('*.py')):add(path,'handwritten_generator_or_guard')
for path in sorted(STAGE.glob('*.lean.txt')):add(path,'handwritten_proof_or_control_template')
for name in modules:add(PROJECT/'ShielddSecurity'/(name+'.lean'),'generated_instance' if name in generated else 'handwritten_helper_or_import_floor')
for name in ['lakefile.lean','lake-manifest.json','lean-toolchain']:add(PROJECT/name,'frozen_package_identity')
for path in sorted(set(fresh_receipt_paths)):
 add(path,'fresh_pass_or_failure_receipt');add(path.with_suffix('.log'),'raw_observation_local_only',False)
for path in sorted(OUT.glob('*.json')):
 if path.name.startswith(('publication-','build-','seal-guard','official-imports')):continue
 add(path,'full_descriptor_local_only' if path.name in ['second-tail01.json','second-tail02.json'] else 'qualified_data_or_provenance_or_generator_metadata',path.name not in ['second-tail01.json','second-tail02.json'])
for path in sorted(official_manifests):add(path,'deduplicated_official_import_closure')
for path in sorted(OUT.glob('seal-guard*.json')):add(path,'preserved_seal_wrapper_failure_zero_proof_credit');add(path.with_suffix('.log'),'raw_observation_local_only',False)
for path in sorted(OUT.glob('selection-guard*.log')):add(path,'raw_observation_local_only',False)
for path in sorted((OUT/'source-history').glob('*')):
 if path.is_file():add(path,'preserved_predecessor_zero_failure_credit')
assert len({x['path'] for x in files})==len(files)
manifest=dict(schema='finite-poseidon-second-tail-publication-v1',runtime_sha=before['runtime_sha'],files=files,current_pass_receipts=receipts,inherited_imports=inherited_imports,inherited_packet=inherited,source_objects_not_published=True,full_descriptor_local_only=True,raw_logs='local only; post-run envelope binds active guard receipt/log without self-reference',failures='preserved zero credit',full_transfer='OPEN')
path=OUT/'publication-manifest01.json';assert not path.exists();path.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(status='passed',manifest_sha256=sha(path),files=len(files),publication_files=sum(x['publication'] for x in files),modules=len(modules),audits=summary['fresh_audits'],core_source_bytes=summary['core_source_bytes'],core_object_bytes=summary['core_object_bytes'],core_build_seconds=summary['core_build_seconds'],seconds=time.monotonic()-started)),flush=True)
