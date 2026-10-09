"""Freeze exact Upstream11 source/object/receipt provenance without kernel replay."""
import hashlib,json,re,subprocess,time
from pathlib import Path
from audit_log import validate
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-width6-upstream11';P=S/'project'
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while chunk:=f.read(1024**2):h.update(chunk)
 return h.hexdigest()
def ident(path):return dict(sha256=sha(path),bytes=path.stat().st_size)
def snapshot():
 descriptor=O/'upstream01.json';assert sha(descriptor)=='3be245c6c55f473352481dbbc43d876591f8bbcedb61bd9c9c633de785112d6e';d=json.loads(descriptor.read_bytes())
 pr=R/'outputs/mac-transfer-pilot01/provenance-successor01.json';assert sha(pr)==d['provenance_receipt_sha256'];v=json.loads(pr.read_bytes());assert v['runtime_sha']==d['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a';assert str(v['modulus'])==d['modulus']
 baseline=R/'work/runtime-snapshot';runtime=R/'work/parent-full-program/runtime';assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=baseline,text=True).strip()==d['runtime_sha'];assert not subprocess.check_output(['git','status','--porcelain'],cwd=baseline,text=True).strip()
 assert len(v['runtime_sources'])==1209
 for item in v['runtime_sources']:
  assert sha(baseline/item['path'])==item['baseline_sha256'];assert sha(runtime/item['path'])==item['capture_sha256']
 assert sum(x['baseline_sha256']!=x['capture_sha256'] for x in v['runtime_sources'])==4
 inputs={name:ident(R/'work/parent-full-program/capture'/name) for name in d['qualified_inputs']};assert inputs==d['qualified_inputs']==v['inputs']
 for item in d['qualified_reader_sources']:assert sha(R/'work/mac-m18-framing01'/item['path'])==item['sha256']
 params='crates/crypto/primitives/params/poseidon381-wide.json';assert sha(baseline/params)==sha(runtime/params)==d['parameter_sha256']
 assert json.loads((baseline/params).read_bytes())==d['parameters']
 return dict(runtime_sha=d['runtime_sha'],modulus=d['modulus'],descriptor_sha256=sha(descriptor),capture_inputs=inputs,parameter_sha256=d['parameter_sha256'],provenance_sha256=sha(pr),baseline_sources=1209,diagnostic_overlays=4,clean_source_verifier_vk_correspondence='OPEN')
started=time.monotonic();before=snapshot();packet=json.loads((O/'input-packet02.json').read_bytes());attempts=[]
for rp in O.glob('build-*.json'):
 v=json.loads(rp.read_bytes())
 if v.get('command',[])[-1:]==[str(P/'ShielddSecurity'/(v['module']+'.lean'))]:attempts.append((rp,v))
passed=[(p,v) for p,v in attempts if v['status']=='passed'];failed=[(p,v) for p,v in attempts if v['status']!='passed'];assert len(passed)==87 and len(failed)==11
current={};inherited={};cost=[];official=set();guard_hashes=set()
guard_candidates=list(S.glob('*.py'))+list((O/'source-history').glob('*.py'))
for rp,v in passed:
 name=v['module'];src=P/'ShielddSecurity'/(name+'.lean');obj=P/'.lake/build/lib/lean/ShielddSecurity'/(name+'.olean');assert sha(src)==v['source_sha256'] and sha(obj)==v['object_sha256']
 assert '-j1' in v['command'] and '-M2048' in v['command'];assert v['timeout_seconds']==240 and v['process_group_rss_limit_bytes']==4*1024**3
 assert v['minimum_memory_free_percent']>=15 and v['minimum_disk_free_bytes']>=2*1024**3
 log=rp.with_suffix('.log');assert sha(log)==v['log_sha256'];a=validate(log.read_text(),v['expected_axiom_names'],v['expected_signature_names']);assert a['axiom_audits']==v['axiom_audits']
 for guard,h in v['guard_sources_sha256'].items():assert any(sha(x)==h for x in guard_candidates),guard;guard_hashes.add(h)
 for n,item in v['frozen_imports'].items():
  if not n.startswith('ShielddSecurity.'):continue
  sp=P/(n.replace('.','/')+'.lean');op=P/'.lake/build/lib/lean'/(n.replace('.','/')+'.olean');assert sha(sp)==item['source_sha256'] and sha(op)==item['object_sha256'],n
  short=n.removeprefix('ShielddSecurity.')
  if short not in {x['module'] for _,x in passed}:
   orig=packet['reused'][short];assert orig['source_sha256']==sha(sp) and orig['object_sha256']==sha(op);assert sha(R/orig['original_receipt_path'])==orig['original_receipt_sha256'];inherited[n]=dict(**orig,source_path=str(sp.relative_to(R)),fresh_execution_credit=0)
 for k,namefile in [('lakefile_sha256','lakefile.lean'),('lake_manifest_sha256','lake-manifest.json'),('toolchain_sha256','lean-toolchain')]:assert sha(P/namefile)==v['frozen_imports']['package'][k]
 c=v['frozen_imports']['official_import_closure'];f=O/c['manifest_file'];assert sha(f)==c['manifest_sha256'];official.add(f)
 current[name]=dict(receipt=str(rp.relative_to(R)),receipt_sha256=sha(rp),source_sha256=sha(src),object_sha256=sha(obj),audits=a['axiom_audits'])
 cost.append(dict(module=name,source_bytes=src.stat().st_size,object_bytes=obj.stat().st_size,seconds=v['seconds'],peak_group_rss_bytes=v['peak_group_rss_bytes'],audits=a['axiom_audits']))
assert len(current)==87 and sum(c['audits'] for c in cost)==496
failures=[]
for rp,v in failed:
 assert sha(rp.with_suffix('.log'))==v['log_sha256'];assert any(sha(x)==v['source_sha256'] for x in (O/'source-history').glob('*')),v['module']
 failures.append(dict(receipt=str(rp.relative_to(R)),source_sha256=v['source_sha256'],exit=v['exit'],reason=v['reason'],proof_credit=0))
math=S/'review-snapshot02/manifest.json';m=json.loads(math.read_bytes())
for item in m['files']:
 if item['path'].endswith('.lean'):assert sha(R/item['source_path'])==item['sha256']
portable=S/'review-portable03/manifest.json';m=json.loads(portable.read_bytes())
for item in m['files']:assert sha(R/item['source_path'])==item['sha256']
inv=O/'replay-inventory01.json';i=json.loads(inv.read_bytes());replay=S/'replay02/replay-result.json';r=json.loads(replay.read_bytes());assert r['status']=='passed' and r['generated_sources']==85 and r['inventory_sha256']==sha(inv)
for name,h in i['maintained'].items():assert sha(S/name)==h
for name,item in i['generated'].items():assert ident(P/'ShielddSecurity'/(name+'.lean'))==item
for name,h in i['handwritten_helpers'].items():assert sha(P/'ShielddSecurity'/name)==h
assert sha(O/'portable-input01.json')==r['portable_input_sha256']==i['portable_input_sha256']
after=snapshot();assert before==after
summary=dict(status='passed',published_ACK='9489b759610e5026b9e5b8cb55ff40022b4e72c8',fresh_module_executions=87,fresh_fulltype_audits=496,fresh_axiom_audits=496,noncost_modules=86,noncost_audits=495,cost_only_marker=1,current_pass=current,inherited_modules=len(inherited),inherited_execution_credit=0,upstream=dict(domain=17,arity=9,IV=2321,permutations=2,materialized_steps=627,steps=628,arithmetic_rows=836,rows=837,capture_indices=[38040,38875],copy_capture=200769,writes=[60778,61613]),joined=dict(materialized_steps=864,steps=865,arithmetic_rows=1152,rows=1153,capture_indices=[38040,39191],copy_capture=200769,writes=[60778,61929]),controls=dict(rejections=8,semantic_inequality_claim=False,scope='B0R00-only exact syntax checks and domain/arity/input metadata, plus fixed carry/child LC comparison; missing_copy removes B0R00 own copy, not the joined shared copy; wrong MDS/source port affect B0R00 only'),costs=cost,total_source_bytes=sum(x['source_bytes'] for x in cost),total_object_bytes=sum(x['object_bytes'] for x in cost),total_seconds=sum(x['seconds'] for x in cost),peak_group_rss_bytes=max(x['peak_group_rss_bytes'] for x in cost),import_floor=next(x for x in cost if 'ImportFloor' in x['module']),RSS_note='Sampled total process-group RSS, not marginal heap attribution',failed_lean_attempts=failures,other_zero_credit_failures=['selection-guard01 source-data qualification failed; successor02 passed','prelaunch missing cached TailTemplate05Program01 import artifact; import-extension01 supplied exact inherited objects, no Lean launched'],math_review_snapshot_sha256=sha(math),portable_review_snapshot_sha256=sha(portable),portable_replay=dict(result=str(replay.relative_to(R)),sha256=sha(replay),generated_sources=85,input_sha256=sha(O/'portable-input01.json')),explicit_guard_histories=sorted(guard_hashes),limits=dict(LEAN_NUM_THREADS=1,j=1,heap_MiB=2048,seconds=240,group_RSS_bytes=4*1024**3,memory_free_percent=15,disk_free_bytes=2*1024**3),scope='SAME final-rho cut-LC independent domain17 nine-input hash6 (two permutations) joined to accepted domain18 one-input hash3; exact selected local row construction and capture INDEX partitions.',open=['Strong arbitrary whole-call candidate guard-to-kernel bridge','External cuts129141/129144 semantic evaluation','Native runtime callsite/raw parent consumer identity','Formal positional rowAt parent-page/full200770relation inclusion for new upstream rows','Later consumer rows','Clean baseline/verifier/VK correspondence','Full Transfer theorem'],full_transfer='OPEN',source_review_acceptance='Await orchestrator final disposition')
(O/'whole-upstream-result01.json').write_text(json.dumps(summary,indent=2)+'\n');(O/'seal-provenance01.json').write_text(json.dumps(dict(status='passed',before=before,after_equal_before=True,inherited_imports=inherited,seconds=time.monotonic()-started),indent=2)+'\n')
files=[]
def add(p,category,publish=True):
 path=str(p.relative_to(R))
 if any(x['path']==path for x in files):return
 files.append(dict(path=path,category=category,publication=publish,**ident(p)))
for p in S.glob('*.py'):add(p,'maintained_generator_helper_or_guard')
for p in S.glob('*.lean.txt'):add(p,'maintained_template')
for name in current:add(P/'ShielddSecurity'/(name+'.lean'),'generated_instance' if name in i['generated'] else 'handwritten_helper')
for p,v in attempts:add(p,'fresh_pass_or_failure_receipt');add(p.with_suffix('.log'),'raw_observation',False)
for p in official:add(p,'official_import_closure_manifest')
for p in O.glob('*.json'):
 if p.name.startswith(('build-','official-imports','publication-','seal-guard')):continue
 add(p,'qualified_input_or_result',p.name!='upstream01.json')
for p in (O/'source-history').glob('*'):add(p,'failure_source_or_maintained_predecessor')
for name in ['lakefile.lean','lake-manifest.json','lean-toolchain']:add(P/name,'package_identity')
for p in [math,portable,replay]:add(p,'immutable_review_or_replay_manifest')
manifest=O/'publication-manifest01.json';assert not manifest.exists();manifest.write_text(json.dumps(dict(schema='finite-upstream11-packet-v1',files=files,receipts=current,inherited_imports=inherited,raw_logs_local_only=True,full_descriptor_local_only=True,no_git_writes=True,scope=summary['scope']),indent=2)+'\n')
print(json.dumps(dict(status='passed',manifest=str(manifest),sha256=sha(manifest),files=len(files),fresh=87,audits=496,inherited=len(inherited),seconds=time.monotonic()-started)))
