"""Seal the finite second-width3-tail/page instance. No build or source mutation."""
import hashlib,json,re,subprocess,time
from pathlib import Path
from audit_log import validate
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-width3-rename09';P=S/'project'
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return h.hexdigest()
def ident(path):return dict(sha256=sha(path),bytes=path.stat().st_size)
def snapshot():
 descriptor=O/'second-tail01.json';assert sha(descriptor)=='a9c0764846ed7c31012f295f3d4f77b952bcff27ce43d4b14c66d92e14ee43ae';d=json.loads(descriptor.read_text());pr=R/'outputs/mac-transfer-pilot01/provenance-successor01.json';assert sha(pr)==d['provenance_receipt_sha256'];p=json.loads(pr.read_text());assert p['runtime_sha']==d['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a';assert p['modulus']==d['modulus'];baseline=R/'work/runtime-snapshot';runtime=R/'work/parent-full-program/runtime'
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=baseline,text=True).strip()==d['runtime_sha'];assert not subprocess.check_output(['git','status','--porcelain'],cwd=baseline,text=True).strip()
 pin=R/'outputs/mac-row-replay/pinned-inputs.json';assert sha(pin)==p['runtime_manifest_sha256'];assert len(p['runtime_sources'])==1209
 for item in p['runtime_sources']:
  assert sha(baseline/item['path'])==item['baseline_sha256'];assert sha(runtime/item['path'])==item['capture_sha256']
 assert sum(i['baseline_sha256']!=i['capture_sha256'] for i in p['runtime_sources'])==4
 inputs={n:ident(R/'work/parent-full-program/capture'/n) for n in d['qualified_inputs']};assert inputs==d['qualified_inputs']==p['inputs']
 for path,h in d['source_guards'].items():assert sha(R/path)==h,path
 for item in d['qualified_reader_sources']:assert sha(R/'work/mac-m18-framing01'/item['path'])==item['sha256']
 parameter=baseline/'crates/crypto/primitives/params/poseidon381.json';assert sha(parameter)==d['parameter_sha256']=='f45040142a56e16bb8480f1f6648621d32f456646cfaf77beca2b05a6bb12742'
 return dict(runtime_sha=d['runtime_sha'],modulus=d['modulus'],capture_inputs=inputs,parameter_sha256=sha(parameter),descriptor_sha256=sha(descriptor),reader_sources=d['qualified_reader_sources'],provenance_sha256=sha(pr),runtime_manifest_sha256=sha(pin),baseline_sources=1209,diagnostic_overlays=4,clean_source_verifier_vk_correspondence='OPEN')
started=time.monotonic();before=snapshot();packet=json.loads((O/'input-packet01.json').read_text());names=sorted(p.stem for p in (P/'ShielddSecurity').glob('*.lean') if any(token in p.stem for token in ['Width3SecondTail09','Width3Tail09','Width3ParentPage09','Width3Rename09']) or p.stem in ['CompilerPageSelection09','PoseidonRoundSuffix09']);assert len(names)==48,len(names)
current={};attempts=[];cost=[];inherited={};official=set()
for name in names:
 src=P/'ShielddSecurity'/f'{name}.lean';obj=P/'.lake/build/lib/lean/ShielddSecurity'/f'{name}.olean';matches=[]
 for rp in sorted(O.glob(f'build-{name}-*.json')):
  v=json.loads(rp.read_text());attempts.append(rp)
  if v['status']=='passed' and v['source_sha256']==sha(src) and v['object_sha256']==sha(obj):matches.append((rp,v))
 assert len(matches)==1,(name,'unexpected repeated accepted execution')
 rp,v=matches[0];assert not v.get('reused_from_exact_pass_receipt');assert v['command'][-1]==str(src);assert '-j1' in v['command'] and '-M2048' in v['command'];assert v['timeout_seconds']==240 and v['process_group_rss_limit_bytes']==4*1024**3 and v['lean_heap_limit_MiB']==2048
 log=rp.with_suffix('.log');assert sha(log)==v['log_sha256'];a=validate(log.read_text(),v['expected_axiom_names'],v['expected_signature_names']);assert a['axiom_audits']==v['axiom_audits']
 for n,item in v['frozen_imports'].items():
  if not n.startswith('ShielddSecurity.'):continue
  sp=P/(n.replace('.','/')+'.lean');op=P/'.lake/build/lib/lean'/(n.replace('.','/')+'.olean');assert sha(sp)==item['source_sha256'] and sha(op)==item['object_sha256'],n
  short=n.removeprefix('ShielddSecurity.')
  if short not in names:
   orig=packet['reused'][short];assert orig['source_sha256']==sha(sp) and orig['object_sha256']==sha(op);assert sha(R/orig['original_receipt_path'])==orig['original_receipt_sha256'];inherited[n]=dict(**orig,source_path=str(sp.relative_to(R)),credit='inherited exact source/object/receipt, zero fresh execution')
 official.add(O/v['frozen_imports']['official_import_closure']['manifest_file']);assert sha(O/v['frozen_imports']['official_import_closure']['manifest_file'])==v['frozen_imports']['official_import_closure']['manifest_sha256']
 current[name]=dict(receipt=str(rp.relative_to(R)),receipt_sha256=sha(rp),source_sha256=sha(src),object_sha256=sha(obj),audits=a['axiom_audits']);cost.append(dict(module=name,source_bytes=src.stat().st_size,object_bytes=obj.stat().st_size,seconds=v['seconds'],peak_group_rss_bytes=v['peak_group_rss_bytes'],audits=a['axiom_audits']))
review=S/'review-snapshot02/manifest.json';frozen=json.loads(review.read_text());
for item in frozen['files']:
 if item['path'].startswith('project/') or item['path'].startswith('maintained/'):
  live=S/item['path'] if item['path'].startswith('project/') else S/Path(item['path']).name
  assert sha(live)==item['sha256'],live
replay=R/'work/rename09-repro02/outputs/mac-poseidon-width3-rename09/replay-result01.json';replayed=json.loads(replay.read_text());assert replayed['status']=='passed' and len(replayed['sources'])==46
for item in replayed['sources']:assert sha(P/'ShielddSecurity'/(item['module']+'.lean'))==item['sha256']
for name,h in replayed['maintained_inputs'].items():assert sha(S/name)==h
assert sha(S/'verify_replay.py')==replayed['recipe_sha256'];after=snapshot();assert before==after
failures=[dict(receipt=str(p.relative_to(R)),**{k:v.get(k) for k in ['source_sha256','exit','reason','status']},proof_credit=0) for p in attempts if (v:=json.loads(p.read_text()))['status']!='passed'];assert len(failures)==1
floor=next(x for x in cost if 'ImportFloor' in x['module']);scope='Second captured width3 rounds2..64 tail: arbitrary target assignment,225 materialized+onecopy construction for300actualtailrows+copy, exact selected inclusion into parentpage38400..39423+copy200769,492actualpriorpagerows preserved conditionally. No later-consumer/fullpage construction, no absorption/native/upstream/globalfullrelation join.'
summary=dict(status='passed',scope=scope,current_pass=current,fresh_module_executions=len(names),fresh_axiom_audits=sum(c['audits'] for c in cost),fresh_fulltype_audits=sum(c['audits'] for c in cost),import_floor_is_cost_only=True,inherited_modules=len(inherited),inherited_fresh_execution=0,selected_tail_rows=300,copy_rows=1,source_tail_nodes=[364076,365623],source_census_includes_round1=[364046,365623],source_tail_nodes_count=1548,phase_boundaries=63,steps=226,materialized_steps=225,page_rows=1024,page_with_copy_rows=1025,prior_page_rows=492,writes=[61630,61929],cuts=[61620,61624,61628],controls=dict(positive=2,rejections=7,guard_rejections=2,semantic_inequality_claim=False),costs=cost,total_source_bytes=sum(c['source_bytes'] for c in cost),total_object_bytes=sum(c['object_bytes'] for c in cost),total_seconds=sum(c['seconds'] for c in cost),peak_group_rss_bytes=max(c['peak_group_rss_bytes'] for c in cost),import_floor=floor,RSS_difference_note='Sampled total RSS differences are observations, not marginal-heap/import-floor explanation.',failures=failures,replay=dict(result=str(replay.relative_to(R)),sha256=sha(replay),generated_sources=46),review_snapshot_sha256=sha(review),source_review_acceptance='Await orchestrator Opus disposition',limits=dict(LEAN_NUM_THREADS=1,j=1,heap_MiB=2048,seconds=240,group_RSS_bytes=4*1024**3),full_transfer='OPEN',open=['Target domain18/arity1 absorption/first two rounds','Later consumer-row preservation','Full200770-parent inclusion/partition','Native/runtime call identity and upstream-cut closure','Clean baseline/verifier/VK correspondence','Full Transfer theorem'])
(O/'tail-page-result01.json').write_text(json.dumps(summary,indent=2)+'\n');(O/'seal-provenance01.json').write_text(json.dumps(dict(status='passed',before=before,after_equal_before=True,inherited_imports=inherited,review_snapshot_sha256=sha(review),seconds=time.monotonic()-started),indent=2)+'\n')
files=[]
def add(path,category,publish=True):
 rel=str(path.relative_to(R))
 if any(i['path']==rel for i in files):return
 files.append(dict(path=rel,category=category,publication=publish,**ident(path)))
for p in sorted(S.glob('*.py')):add(p,'maintained_generator_or_guard')
for p in sorted(S.glob('*.lean.txt')):add(p,'maintained_template')
generated={i['module'] for i in replayed['sources']}
for name in names:add(P/'ShielddSecurity'/f'{name}.lean','generated_instance' if name in generated else 'handwritten_helper')
for n in ['lakefile.lean','lake-manifest.json','lean-toolchain']:add(P/n,'package_identity')
for p in attempts:add(p,'fresh_pass_or_failure_receipt');add(p.with_suffix('.log'),'raw_observation',False)
for p in sorted(official):add(p,'official_closure_identity')
for p in sorted(O.glob('*.json')):
 if p.name.startswith(('build-','official-imports','publication-','seal-guard')):continue
 add(p,'local_full_descriptor' if p.name=='second-tail01.json' else 'qualified_input_or_result',p.name!='second-tail01.json')
for p in sorted((O/'source-history').glob('*')):add(p,'failure_or_representation_predecessor')
add(replay,'portable_replay_result');add(review,'source_review_manifest');
manifest=O/'publication-manifest01.json';assert not manifest.exists();manifest.write_text(json.dumps(dict(schema='finite-width3-tail-page-packet-v1',scope=scope,files=files,receipts=current,inherited_imports=inherited,raw_logs_local_only=True,no_git_writes=True),indent=2)+'\n');print(json.dumps(dict(status='passed',manifest=str(manifest),sha256=sha(manifest),files=len(files),fresh=len(names),audits=summary['fresh_axiom_audits'],seconds=time.monotonic()-started)))
