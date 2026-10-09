"""Seal this finite measured instance; raw logs stay local and are hash-bound."""
import hashlib,json,subprocess,time
from pathlib import Path
STAGE=Path(__file__).resolve().parent; ROOT=STAGE.parents[1]
OUT=ROOT/'outputs/mac-poseidon-round01'; PROJECT=STAGE/'project'
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
started=time.monotonic();before=snapshot()
fixed=['CompilerRecord01','CompilerIndexCoverage01','CompilerPriorFrame01','Poseidon','PoseidonRoundComposition',
 'PoseidonIndexedRound01','SourceGraphNodeValues01','TransferPoseidonRoundImportFloor01']
suffixes=['Tables01','Data01','Leaf01','Leaf02','Program01','Proof01','SemanticData01','SemanticChecks01',
 'SemanticProof01','SemanticControlsData01','SemanticControls01']
modules=fixed+[f'TransferPoseidonRound{tag}{suffix}' for tag in ['01','04'] for suffix in suffixes]
generated=[n for n in modules if n not in fixed];receipts={};costs=[]
for name in modules:
 source=PROJECT/'ShielddSecurity'/(name+'.lean');obj=PROJECT/'.lake/build/lib/lean/ShielddSecurity'/(name+'.olean')
 matching=[]
 for path in sorted(OUT.glob('build-'+name+'-*.json')):
  result=json.loads(path.read_text())
  if result['status']=='passed' and result['source_sha256']==sha(source) and result['object_sha256']==sha(obj):matching.append((path,result))
 assert matching,'unqualified current source/object: '+name
 path,result=matching[-1]
 for imported,item in result['frozen_imports'].items():
  if not imported.startswith('ShielddSecurity.'):continue
  assert sha(PROJECT/(imported.replace('.','/')+'.lean'))==item['source_sha256'],imported
  assert sha(PROJECT/'.lake/build/lib/lean'/(imported.replace('.','/')+'.olean'))==item['object_sha256'],imported
 official=result['frozen_imports']['official_import_closure']
 assert sha(OUT/official['manifest_file'])==official['manifest_sha256']
 receipts[name]=dict(path=str(path.relative_to(ROOT)),sha256=sha(path),audits=result['axiom_audits'])
 costs.append(dict(module=name,source_bytes=source.stat().st_size,object_bytes=obj.stat().st_size,
  seconds=result['seconds'],peak_group_rss_bytes=result['peak_group_rss_bytes'],audits=result['axiom_audits']))
expected={n:sha(PROJECT/'ShielddSecurity'/(n+'.lean')) for n in generated}
for script in ['generate_rounds.py','generate_round_proofs.py','generate_round_semantics.py','diagnose_semantic.py',
 'generate_round_semantic_proofs.py','generate_round_semantic_controls.py']:
 subprocess.run(['python3',str(STAGE/script)],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
assert expected=={n:sha(PROJECT/'ShielddSecurity'/(n+'.lean')) for n in generated}
after=snapshot();assert before==after
provenance=dict(status='passed',before=before,after_equal_before=True,generated_sources_equal=True,
 mathematical_rounds=[1,4],native_folded_round0='DATA ONLY',
 parameter_interpretation='exact selected ARK row and all MDS coefficients; full65 ARK function join OPEN',
 cut_interpretation='six prior state LC values of one arbitrary prior assignment; no independent six-witness allocation',
 copy_link='explicit prior base copy=base0 for extension; actual original copy row for arbitrary-rho soundness',
 seconds=time.monotonic()-started)
(OUT/'seal-provenance01.json').write_text(json.dumps(provenance,indent=2)+'\n')
failures=[]
for path in sorted(OUT.glob('build-*.json')):
 result=json.loads(path.read_text())
 if result['status']!='passed':failures.append(dict(receipt=str(path.relative_to(ROOT)),source_sha256=result['source_sha256'],
  status=result['status'],exit=result.get('exit'),reason=result.get('reason'),proof_credit=0))
floor=next(x for x in costs if x['module']=='TransferPoseidonRoundImportFloor01')
core=[x for x in costs if not any(t in x['module'] for t in ['Controls','ImportFloor','SourceGraphNodeValues'])]
summary=dict(schema='bounded-poseidon-round-result-v1',status='passed',runtime_sha=before['runtime_sha'],
 scope=[dict(round=1,source_nodes=[577,672],typed_nodes=150,arithmetic_nodes=96,constant_leaves=48,prior_cut_leaves=6,
  raw_rows=list(range(338,362))+[200769],max_LC_terms=6),
  dict(round=4,source_nodes=[865,945],typed_nodes=135,arithmetic_nodes=81,constant_leaves=48,prior_cut_leaves=6,
  raw_rows=list(range(410,414))+[200769],max_LC_terms=8)],
 qualified_data_only=dict(round0_source_nodes=[503,576],all251_arithmetic_nodes=True,unique_raw_rows=45),
 certificates=dict(all_typed_node_certificates=True,all_index_coverage=True,actual_copy_link=True,
  exact_both_direction_row_coverage=True,topological=True,legal_materialization_independent_of_assertions=True,
  arbitrary_rho_source_graph_and_independent_round=True,total_assignment=True,all22735_original_inputs_preserved=True,
  prior0_public_committed_columns_preserved=True,prior_copy_and_cut_LCs_preserved=True,
  prior_copy_link_is_explicit_domain_condition=True,round_assertion_assumptions=False),
 controls=dict(ARK_delta_one='same productionCheck=false with fixed original rows',
  MDS_delta_one='same productionCheck=false with fixed original rows',
  non_equivalent_state_port='same productionCheck=false with fixed original rows; binding guard rejection',
  wrong_existing_fifth_row='same productionCheck=false',
  raw_coefficient_delta_one='same productionCheck=false; actual mutation and unchanged other rows checked',
  compiler_errors_and_resource_failures_credit=0),
 representation=dict(records='proof-free checked input/constant/add/mul',
  node_blocks='indexed leaves of at most128',semantic_checks='six column/nonlinear and six MDS facts composed symbolically into identical production Bool',
  control_checks='computational facts separated from generic symbolic rejection wrappers'),
 core_source_bytes=sum(x['source_bytes'] for x in core),core_object_bytes=sum(x['object_bytes'] for x in core),
 core_build_seconds=sum(x['seconds'] for x in core),module_costs=costs,audits=sum(x['audits'] for x in costs),
 import_floor=floor,semantic_proof_RSS_minus_floor={x['module']:x['peak_group_rss_bytes']-floor['peak_group_rss_bytes'] for x in costs if 'SemanticProof' in x['module']},
 RSS_note='sampled total process-group RSS differences; not exact heap costs',
 failure_credit=0,failures=failures,
 wrapper_failure='initial accepted eight leaf builds followed by overlong aggregate filename; summary naming fixed without unchanged leaf rerun',
 limits=dict(lean_threads=1,heap_MiB=2048,rss_bytes=4*1024**3,seconds_per_module=240),
 open=['native folded round0','exact65 ARK function join','cut-output to next-input identities','upstream cut closure',
  'global copy initialization','full65 compiler/semantic composition','all-transfer row partition/order',
  'clean-source verifier/VK correspondence','full Transfer theorem'],full_scale_claim=False,full_transfer='OPEN')
(OUT/'round-result01.json').write_text(json.dumps(summary,indent=2)+'\n')
files=[]
def add(path,category,publication=True):files.append(dict(path=str(path.relative_to(ROOT)),category=category,publication=publication,**identity(path)))
for path in sorted(STAGE.glob('*.py')):add(path,'handwritten_generator_or_guard')
for path in sorted(STAGE.glob('*.lean.txt')):add(path,'handwritten_proof_or_control_template')
for name in modules:add(PROJECT/'ShielddSecurity'/(name+'.lean'),'generated_instance' if name in generated else 'handwritten_helper_or_import_floor')
for name in ['lakefile.lean','lake-manifest.json','lean-toolchain']:add(PROJECT/name,'frozen_package_identity')
for path in sorted(OUT.glob('*.json')):
 if path.name.startswith(('publication-manifest','publication-envelope')):continue
 add(path,'receipt_or_immutable_data' if 'generation' not in path.name else 'generator_metadata')
for path in sorted((OUT/'source-history').glob('*')):
 if path.is_file():add(path,'preserved_predecessor_zero_failure_credit')
for name in ['parent-match.py','parent-descriptor.json']:
 path=STAGE/name
 if not any(x['path']==str(path.relative_to(ROOT)) for x in files):add(path,'frozen_parent_input')
for path in sorted(OUT.glob('*.log')):
 if not path.name.startswith('seal-guard'):add(path,'raw_observation_local_only',False)
assert len({x['path'] for x in files})==len(files)
manifest=dict(schema='finite-poseidon-round-publication-v1',runtime_sha=before['runtime_sha'],files=files,
 current_pass_receipts=receipts,source_objects_not_published=True,
 raw_logs='local only; active seal guard receipt/log bound by post-run envelope, never self-referenced',
 inherited_source_packet=dict(path='outputs/mac-poseidon-round01/input-packet01.json',sha256=sha(OUT/'input-packet01.json')),
 failures='preserved, zero credit',full_transfer='OPEN')
path=OUT/'publication-manifest01.json';assert not path.exists();path.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(status='passed',manifest_sha256=sha(path),files=len(files),publication_files=sum(x['publication'] for x in files),
 core_source_bytes=summary['core_source_bytes'],core_object_bytes=summary['core_object_bytes'],core_build_seconds=summary['core_build_seconds'],audits=summary['audits'],seconds=time.monotonic()-started)),flush=True)
