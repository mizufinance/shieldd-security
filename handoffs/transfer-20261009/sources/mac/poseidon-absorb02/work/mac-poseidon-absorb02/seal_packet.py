"""Seal this finite measured instance; raw logs stay local and are hash-bound."""
import hashlib,json,subprocess,time
from pathlib import Path
STAGE=Path(__file__).resolve().parent; ROOT=STAGE.parents[1]
OUT=ROOT/'outputs/mac-poseidon-absorb02'; PROJECT=STAGE/'project'
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as stream:
  while b:=stream.read(1024**2):h.update(b)
 return h.hexdigest()
def identity(path):return dict(bytes=path.stat().st_size,sha256=sha(path))
def snapshot():
 d=json.loads((OUT/'rounds03.json').read_text()); provenance=ROOT/'outputs/mac-transfer-pilot01/provenance-successor01.json'
 assert sha(OUT/'rounds03.json')=='e810d2f6c957ee1e3263409c92bd26a0fda21da6f3cd5e41bf526b747a9904a3'
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
 parameter=baseline/'crates/crypto/primitives/params/poseidon381-wide.json'
 assert sha(parameter)==d['parameter_sha256']=='84a51d11b64641fc3604b4cbedbe7cc82e91204b21d3bd62fb59462bbb4a5bb8'
 for name,item in d['parent_inputs'].items():assert sha(ROOT/item['path'])==item['sha256']
 for path,h in d['source_guard_identities'].items():assert sha(ROOT/path)==h
 return dict(parameter_sha256=sha(parameter),runtime_sha=d['runtime_sha'],modulus=d['modulus'],inputs=inputs,
   descriptor_sha256=sha(OUT/'rounds03.json'),provenance_receipt_sha256=sha(provenance),
   runtime_manifest_sha256=sha(pinned),runtime_sources_digest=hashlib.sha256(json.dumps(sources,sort_keys=True).encode()).hexdigest(),
   baseline_files_checked=1209,diagnostic_overlays=p['diagnostic_overlays'],qualified_reader_sources=helpers,
   clean_source_verifier_vk_correspondence='OPEN',full_transfer='OPEN')
from audit_log import validate
started=time.monotonic();before=snapshot()
assert sha(ROOT/'outputs/mac-poseidon-round01/publication-manifest01.json')=='412ba30928a38ddd4654a1ddf4f03957b1c21797ce9605036c81ab6bf66001d9'
inherited=json.loads((OUT/'inherited-sealed01.json').read_text())
assert sha(ROOT/inherited['manifest_path'])==inherited['manifest_sha256']
# Inventory is finite and explicit. Inherited sealed proofs are not fresh replays.
handwritten=['CompilerOrderComposition','CompilerRawInclusion02','PoseidonIndexedFolded02','PoseidonFirstTwoChecked02','TransferPoseidonFirstTwoImportFloor02']
generated=['TransferPoseidonAbsorb02'+s for s in ['Tables01','Data01','Leaf01','Program01','Proof01','SemanticData01','SemanticChecks01','SemanticProof01','ControlsData01','Controls01']]+['TransferPoseidonParameters02']+['TransferPoseidonFirstTwo02'+s for s in ['Data01','Proof01','ControlsData01','Controls01']]
modules=handwritten+generated;receipts={};costs=[];inherited_imports={};fresh_receipt_paths=[]
for name in modules:
 source=PROJECT/'ShielddSecurity'/(name+'.lean');obj=PROJECT/'.lake/build/lib/lean/ShielddSecurity'/(name+'.olean')
 matching=[]
 for path in sorted(OUT.glob('build-'+name+'-*.json')):
  result=json.loads(path.read_text())
  if result['status']=='passed' and result['source_sha256']==sha(source) and result['object_sha256']==sha(obj):matching.append((path,result))
 assert matching,'unqualified source/object '+name
 path,result=matching[-1];assert result['command'][-1]==str(source)
 assert result['lean_heap_limit_MiB']==2048 and '-M2048' in result['command'] and '-j1' in result['command']
 log=OUT/path.name.replace('.json','.log');assert sha(log)==result['log_sha256']
 audited=validate(log.read_text(),result['expected_axiom_names'],result['expected_signature_names'])
 assert audited['axiom_audits']==result['axiom_audits']
 for imported,item in result['frozen_imports'].items():
  if not imported.startswith('ShielddSecurity.'):continue
  sourcePath=PROJECT/(imported.replace('.','/')+'.lean');objectPath=PROJECT/'.lake/build/lib/lean'/(imported.replace('.','/')+'.olean')
  assert sha(sourcePath)==item['source_sha256'] and sha(objectPath)==item['object_sha256'],imported
  short=imported.removeprefix('ShielddSecurity.')
  if short not in modules:
   candidates=[]
   for rp in (ROOT/'outputs/mac-poseidon-round01').glob('build-'+short+'-*.json'):
    r=json.loads(rp.read_text())
    if r['status']=='passed' and r['source_sha256']==item['source_sha256'] and r['object_sha256']==item['object_sha256']:candidates.append(rp)
   assert candidates,'unqualified inherited source '+imported
   rp=sorted(candidates)[-1]
   value=dict(**item,source_path=str(sourcePath.relative_to(ROOT)),prior_receipt=str(rp.relative_to(ROOT)),prior_receipt_sha256=sha(rp),credit='inherited sealed proof, not fresh replay')
   if imported in inherited_imports:assert inherited_imports[imported]==value
   inherited_imports[imported]=value
 official=result['frozen_imports']['official_import_closure'];assert sha(OUT/official['manifest_file'])==official['manifest_sha256']
 receipts[name]=dict(path=str(path.relative_to(ROOT)),sha256=sha(path),audits=result['axiom_audits'])
 costs.append(dict(module=name,source_bytes=source.stat().st_size,object_bytes=obj.stat().st_size,seconds=result['seconds'],peak_group_rss_bytes=result['peak_group_rss_bytes'],audits=result['axiom_audits'],heap_MiB=result['lean_heap_limit_MiB']))
 for rp in OUT.glob('build-'+name+'-*.json'):fresh_receipt_paths.append(rp)
expected={name:sha(PROJECT/'ShielddSecurity'/(name+'.lean')) for name in generated}
for script in ['generate_absorption.py','generate_absorption_proof.py','generate_absorption_semantics.py','generate_absorption_checks.py','generate_absorption_semantic_proof.py','generate_first_two.py','generate_first_two_proof.py','generate_controls.py']:
 subprocess.run(['python3',str(STAGE/script)],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
assert expected=={name:sha(PROJECT/'ShielddSecurity'/(name+'.lean')) for name in generated}
after=snapshot();assert before==after
(OUT/'seal-provenance01.json').write_text(json.dumps(dict(status='passed',before=before,after_equal_before=True,generated_sources_equal=True,generated_source_count=len(generated),inherited_packet=inherited,inherited_imports=inherited_imports,scope='original source inputs11/12/18/19, folded absorption round0 then full round1, one global65-row parameter function, one copy row, no source assertion premises',seconds=time.monotonic()-started),indent=2)+'\n')
failures=[]
for path in sorted(set(fresh_receipt_paths)):
 result=json.loads(path.read_text())
 if result['status']!='passed':failures.append(dict(receipt=str(path.relative_to(ROOT)),source_sha256=result['source_sha256'],status=result['status'],exit=result.get('exit'),reason=result.get('reason'),heap_MiB=result['lean_heap_limit_MiB'],proof_credit=0))
floor=next(x for x in costs if 'ImportFloor' in x['module']);core=[x for x in costs if 'Controls' not in x['module'] and 'ImportFloor' not in x['module']]
summary=dict(schema='bounded-poseidon-absorption-two-round-result-v1',status='passed',runtime_sha=before['runtime_sha'],fresh_modules=len(modules),fresh_audits=sum(x['audits'] for x in costs),inherited_proof_replay=False,
 scope=dict(domain=23,arity=4,IV=1047,original_input_indices=[11,12,18,19],round0=dict(source_nodes=[503,576],typed_nodes=122,arithmetic_nodes=74,original_rows=list(range(322,338))),round1=dict(source_nodes=[577,672],typed_nodes=150,arithmetic_nodes=96,original_rows=list(range(338,362))),copy_capture_index=200769,deduplicated_rows=41,materialized_steps=30,shared_copy_step=1,fresh_columns=[23060,23099],max_LC_terms=6),
 certificates=dict(actual_copy_row_link=True,raw_indexed_inclusion=True,reverse_original_row_coverage=True,materialized_topological_order=True,independent_materialization_legal=True,original_four_input_absorption=True,native_constant_folding=True,global_selected_ARK_and_full_MDS_joins=True,exact_boundary_LC_identity=True,earlier_raw_row_support_frame=True,all22735_source_inputs_and_columns0_1_2_preserved=True,prior_copy_preserved=True,arbitrary_rho_to_independent_rounds2=True,total_assignment_all41_original_rows=True,source_assertion_premises=False,prior_copy_link_explicit=True,production_checker_used_by_both_headline_theorems=True),
 controls=dict(absorption=['domain23→22','arity4→5','source11/12 swapped','native constant fifth hint+1'],composition=['non-equivalent boundary port0→1','second first row mapping16→17 canonically different existing row','reverse map40entries vs41 required (guard)','missing shared copy index40 (guard)','ARK1[0]+1','MDS[0][0]+1'],all_same_production_checkers_return_false=True,type_errors_and_timeouts_credit=0),
 module_costs=costs,core_source_bytes=sum(x['source_bytes'] for x in core),core_object_bytes=sum(x['object_bytes'] for x in core),core_build_seconds=sum(x['seconds'] for x in core),all_source_bytes=sum(x['source_bytes'] for x in costs),all_object_bytes=sum(x['object_bytes'] for x in costs),all_build_seconds=sum(x['seconds'] for x in costs),import_floor=floor,
 compiler_proof_RSS_minus_floor={x['module']:x['peak_group_rss_bytes']-floor['peak_group_rss_bytes'] for x in costs if x['module'].endswith('Proof01') or x['module']=='PoseidonFirstTwoChecked02'},RSS_note='sampled group RSS totals and differences; not exact heap usage',
 failures=failures,failure_proof_credit=0,wrapper_preflight_failure='first dependent Data attempt requested before CompilerRawInclusion02 object existed; wrapper refused before Lean; no proof credit',
 limits=dict(lean_threads=1,heap_MiB=2048,heap_per_receipt_authoritative=True,rss_bytes=4*1024**3,seconds_per_module=240),
 open=['exact global captured parent-row inclusion/partition','late64-term LC resource measurement','65-round call closure','all-transfer row/order/native/header/state composition','clean-source verifier/VK correspondence','full Transfer theorem'],full_scale_claim=False,full_transfer='OPEN')
(OUT/'two-round-result01.json').write_text(json.dumps(summary,indent=2)+'\n')
files=[]
def add(path,category,publish=True):files.append(dict(path=str(path.relative_to(ROOT)),category=category,publication=publish,**identity(path)))
for path in sorted(STAGE.glob('*.py')):add(path,'handwritten_generator_or_guard')
for path in sorted(STAGE.glob('*.lean.txt')):add(path,'handwritten_proof_or_control_template')
for name in modules:add(PROJECT/'ShielddSecurity'/(name+'.lean'),'generated_instance' if name in generated else 'handwritten_helper_or_import_floor')
for name in ['lakefile.lean','lake-manifest.json','lean-toolchain']:add(PROJECT/name,'frozen_package_identity')
for path in sorted(set(fresh_receipt_paths)):
 add(path,'fresh_pass_or_failure_receipt')
 log=path.with_suffix('.log');add(log,'raw_observation_local_only',False)
for path in sorted(OUT.glob('*.json')):
 if path in fresh_receipt_paths or path.name.startswith(('publication-','build-','seal-guard')):continue
 add(path,'qualified_data_or_provenance_or_generator_metadata')
for path in sorted((OUT/'source-history').glob('*')):
 if path.is_file():add(path,'preserved_predecessor_zero_failure_credit')
assert len({x['path'] for x in files})==len(files)
manifest=dict(schema='finite-poseidon-two-round-publication-v1',runtime_sha=before['runtime_sha'],files=files,current_pass_receipts=receipts,inherited_imports=inherited_imports,inherited_packet=inherited,source_objects_not_published=True,raw_logs='local only; post-run envelope binds active guard receipt/log without self-reference',failures='preserved zero credit',full_transfer='OPEN')
path=OUT/'publication-manifest01.json';assert not path.exists();path.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(status='passed',manifest_sha256=sha(path),files=len(files),publication_files=sum(x['publication'] for x in files),modules=len(modules),audits=summary['fresh_audits'],core_source_bytes=summary['core_source_bytes'],core_object_bytes=summary['core_object_bytes'],core_build_seconds=summary['core_build_seconds'],seconds=time.monotonic()-started)),flush=True)
