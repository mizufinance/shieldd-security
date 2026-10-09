"""Seal this finite measured instance; raw logs stay local and are hash-bound."""
import hashlib,json,subprocess,time
from pathlib import Path
STAGE=Path(__file__).resolve().parent; ROOT=STAGE.parents[1]
OUT=ROOT/'outputs/mac-long-recipe01'; PROJECT=STAGE/'project'
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as stream:
  while b:=stream.read(1024**2):h.update(b)
 return h.hexdigest()
def identity(path):return dict(bytes=path.stat().st_size,sha256=sha(path))
def snapshot():
 d=json.loads((OUT/'long-chain01.json').read_text()); provenance=ROOT/'outputs/mac-transfer-pilot01/provenance-successor01.json'
 assert sha(OUT/'long-chain01.json')=='a5679e99521f418cb26f8c8c3e2533fe721d0f2ddedd98c794761a0972fd8045'
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
 return dict(runtime_sha=d['runtime_sha'],modulus=d['modulus'],inputs=inputs,
   descriptor_sha256=sha(OUT/'long-chain01.json'),provenance_receipt_sha256=sha(provenance),
   runtime_manifest_sha256=sha(pinned),runtime_sources_digest=hashlib.sha256(json.dumps(sources,sort_keys=True).encode()).hexdigest(),
   baseline_files_checked=1209,diagnostic_overlays=p['diagnostic_overlays'],qualified_reader_sources=helpers,
   clean_source_verifier_vk_correspondence='OPEN',full_transfer='OPEN')
started=time.monotonic(); before=snapshot()
modules=['CompilerRecipe01','CompilerRecipeTree01','TransferLongRecipeRecords01','TransferLongRecipeBounds01',
 'TransferLongRecipeTreeTables01','TransferLongRecipeTreeBounds01','TransferLongRecipeExpressions01',
 'TransferLongRecipeData01','TransferLongRecipeControls01','TransferLongRecipeProof01',
 'TransferLongRecipeNormalize01','TransferLongRecipeImportFloor01']
receipts={}; costs=[]
for name in modules:
 s=PROJECT/'ShielddSecurity'/(name+'.lean');o=PROJECT/'.lake/build/lib/lean/ShielddSecurity'/(name+'.olean')
 matching=[]
 for path in sorted(OUT.glob('build-'+name+'-*.json')):
  result=json.loads(path.read_text())
  if result['status']=='passed' and result['source_sha256']==sha(s) and result['object_sha256']==sha(o):matching.append((path,result))
 assert matching,name
 path,result=matching[-1]
 for imported,v in result['frozen_imports'].items():
  if not imported.startswith('ShielddSecurity.'):continue
  assert sha(PROJECT/(imported.replace('.','/')+'.lean'))==v['source_sha256'],imported
  assert sha(PROJECT/'.lake/build/lib/lean'/(imported.replace('.','/')+'.olean'))==v['object_sha256'],imported
 receipts[name]=dict(path=str(path.relative_to(ROOT)),sha256=sha(path),audits=result['axiom_audits'])
 costs.append(dict(module=name,source_bytes=s.stat().st_size,object_bytes=o.stat().st_size,
   seconds=result['seconds'],peak_group_rss_bytes=result['peak_group_rss_bytes'],audits=result['axiom_audits']))
# Regeneration is atomic; byte identity must hold for every generated source.
generated=['TransferLongRecipeRecords01','TransferLongRecipeBounds01','TransferLongRecipeTreeTables01',
 'TransferLongRecipeTreeBounds01','TransferLongRecipeExpressions01','TransferLongRecipeData01']
expected={n:sha(PROJECT/'ShielddSecurity'/(n+'.lean')) for n in generated}
subprocess.run(['python3',str(STAGE/'generate_recipe.py')],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
assert expected=={n:sha(PROJECT/'ShielddSecurity'/(n+'.lean')) for n in generated}
after=snapshot();assert before==after
provenance=dict(status='passed',before=before,after_equal_before=True,regenerated_source_equal=True,
 exact_consumer_row_index=179156,source_assertion=1202,source_endpoints=[126788,126791],local_endpoints=[1032,1035],
 runtime_outputs='not claimed; endpoints are selected consumer ports',seconds=time.monotonic()-started)
(OUT/'seal-provenance01.json').write_text(json.dumps(provenance,indent=2)+'\n')
core=[x for x in costs if x['module'] not in ['TransferLongRecipeControls01','TransferLongRecipeNormalize01','TransferLongRecipeImportFloor01']]
floor=next(x for x in costs if x['module']=='TransferLongRecipeImportFloor01'); consumer=next(x for x in costs if x['module']=='TransferLongRecipeData01')
failures=[]
for path in sorted(OUT.glob('build-*.json')):
 r=json.loads(path.read_text())
 if r['status']!='passed': failures.append(dict(receipt=str(path.relative_to(ROOT)),source_sha256=r['source_sha256'],status=r['status'],exit=r.get('exit'),reason=r.get('reason'),proof_credit=0))
summary=dict(schema='bounded-long-recipe-result-v1',status='passed',runtime_sha=before['runtime_sha'],
 scope=dict(typed_nodes=1036,arithmetic_nodes=517,input_leaves=258,constant_leaves=261,distinct_constant_values=131,
   flat_intermediate_terms_observed=17156,flat_intermediate_lc_definitions_generated=0,max_observed_node_lc=256,
   derived_left_length=258,derived_right_length=2,actual_row_terms=258,actual_row_index=179156,assertion_index=1202),
 certificates=dict(all_actual_nodes=True,checked_exact_record_lookup=True,actual_indexed_consumer_row=True,
   arbitrary_rho_soundness=True,total_assignment=True,all22735_original_inputs_preserved=True,
   constructive_completeness='conditional on independent source endpoint truth',native_legality='OPEN'),
 controls=dict(coefficient_delta_one='production consumerCheck=false',non_equivalent_earlier_source_port='production consumerCheck=false',compiler_errors_credit=0),
 representation=dict(records='nine lists of at most128, Array.mk of flatten',bounds='chunk-local Bool checks with symbolic append composition',
   lookup='balanced tree with checked cached left sizes and exact flatten/lookup correspondence',evaluation='proof-free fuel + symbolic agreement with existing semantics',
   duplication='record literals currently duplicated in list and tree tables; measured bounded experiment, not full-scale generator'),
 module_costs=costs,core_source_bytes=sum(x['source_bytes'] for x in core),core_object_bytes=sum(x['object_bytes'] for x in core),
 core_build_seconds=sum(x['seconds'] for x in core),audits=sum(x['audits'] for x in costs),
 import_floor=floor,consumer=consumer,consumer_minus_floor_rss_bytes=consumer['peak_group_rss_bytes']-floor['peak_group_rss_bytes'],
 rss_delta_note='sampled total process-group RSS difference, not an exact heap measurement',
 failure_credit=0,failures=failures,full_transfer='OPEN',limits=dict(lean_threads=1,heap_MiB=2048,rss_bytes=4*1024**3,seconds_per_module=240),
 full_scale_claim=False,next_task='bounded mixed add/scale plus genuine materialized product/square consumers with chunk composition; close global row partition/order and semantic cut ports before scaling')
(OUT/'long-recipe-result01.json').write_text(json.dumps(summary,indent=2)+'\n')
files=[]
def add(path,category,publication=True):files.append(dict(path=str(path.relative_to(ROOT)),category=category,publication=publication,**identity(path)))
for p in sorted(STAGE.glob('*.py')):add(p,'handwritten_runner_or_generator')
for n in modules:add(PROJECT/'ShielddSecurity'/(n+'.lean'),'generated_source' if n in generated else 'handwritten_proof_or_diagnostic')
for p in sorted(OUT.glob('build-*.json')):add(p,'receipt')
for p in sorted((OUT/'source-history').glob('*')):
 if p.is_file():add(p,'preserved_predecessor_source_zero_failure_credit')
for pat in ['generation-*.json','official-imports-*.json']:
 for p in sorted(OUT.glob(pat)):add(p,'generator_metadata' if pat.startswith('generation') else 'immutable_official_import_manifest')
for name in ['input-packet01.json','long-chain01.json','descriptor-result01.json','selection-guard01.json','seal-provenance01.json','long-recipe-result01.json']:
 add(OUT/name,'input_or_result_metadata')
for p in sorted(OUT.glob('*.log')):add(p,'raw_observation_local_only',False)
for n in ['TransferLongRecipeTableShape01','TransferLongRecipePrefix01','TransferLongRecipeCheckOnly01']:
 add(PROJECT/'ShielddSecurity'/(n+'.lean'),'diagnostic_current_source_not_core')
manifest=dict(schema='finite-long-recipe-publication-v1',runtime_sha=before['runtime_sha'],
 files=files,current_pass_receipts=receipts,source_objects_not_published=True,
 package=dict(lakefile=identity(PROJECT/'lakefile.lean'),manifest=identity(PROJECT/'lake-manifest.json'),toolchain=identity(PROJECT/'lean-toolchain')),
 inherited_source_packet=dict(path='outputs/mac-long-recipe01/input-packet01.json',sha256=sha(OUT/'input-packet01.json')),
 raw_logs='retained local with hashes; omitted from publication under repository rule',
 failures='zero credit; prior source variants/receipts retained',full_transfer='OPEN')
path=OUT/'publication-manifest01.json'; assert not path.exists();path.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(status='passed',manifest_sha256=sha(path),files=len(files),publication_files=sum(x['publication'] for x in files),
 core_source_bytes=summary['core_source_bytes'],core_object_bytes=summary['core_object_bytes'],core_build_seconds=summary['core_build_seconds'],audits=summary['audits'],seconds=time.monotonic()-started)))
