"""Freeze finite Call10 receipts and exact inputs; no proof/capture replay."""
import hashlib,json,re,subprocess,time
from pathlib import Path
from audit_log import validate
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-width3-call10';P=S/'project'
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  while b:=f.read(1024**2):h.update(b)
 return h.hexdigest()
def ident(path):return dict(sha256=sha(path),bytes=path.stat().st_size)
def snapshot():
 descriptor=O/'rounds02.json';assert sha(descriptor)=='01b68f32bf6896a6122805713cdd5448105d2aab2da056699c9d35dd57f162ff';d=json.loads(descriptor.read_text())
 pr=R/'outputs/mac-transfer-pilot01/provenance-successor01.json';assert sha(pr)==d['provenance_receipt_sha256'];p=json.loads(pr.read_text());assert p['runtime_sha']==d['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a';assert str(p['modulus'])==d['modulus']
 baseline=R/'work/runtime-snapshot';runtime=R/'work/parent-full-program/runtime'
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=baseline,text=True).strip()==d['runtime_sha'];assert not subprocess.check_output(['git','status','--porcelain'],cwd=baseline,text=True).strip()
 pin=R/'outputs/mac-row-replay/pinned-inputs.json';assert sha(pin)==p['runtime_manifest_sha256'];assert len(p['runtime_sources'])==1209
 for item in p['runtime_sources']:
  assert sha(baseline/item['path'])==item['baseline_sha256'];assert sha(runtime/item['path'])==item['capture_sha256']
 assert sum(i['baseline_sha256']!=i['capture_sha256'] for i in p['runtime_sources'])==4
 inputs={n:ident(R/'work/parent-full-program/capture'/n) for n in d['qualified_inputs']};assert inputs==d['qualified_inputs']==p['inputs']
 for path,h in d['source_guard_identities'].items():assert sha(R/path)==h,path
 for item in d['qualified_reader_sources']:assert sha(R/'work/mac-m18-framing01'/item['path'])==item['sha256']
 return dict(runtime_sha=d['runtime_sha'],modulus=d['modulus'],capture_inputs=inputs,parameter_sha256=d['parameter_sha256'],descriptor_sha256=sha(descriptor),reader_sources=d['qualified_reader_sources'],provenance_sha256=sha(pr),runtime_manifest_sha256=sha(pin),baseline_sources=1209,diagnostic_overlays=4,clean_source_verifier_vk_correspondence='OPEN')
started=time.monotonic();before=snapshot();packet=json.loads((O/'input-packet01.json').read_text());attempts=[];names=set()
for rp in O.glob('build-*.json'):
 v=json.loads(rp.read_text())
 if not v.get('reused_from_exact_pass_receipt') and v.get('command',[])[-1:]==[str(P/'ShielddSecurity'/(v['module']+'.lean'))]:attempts.append(rp);names.add(v['module'])
assert len(names)==22,len(names)
current={};inherited={};cost=[];official=set()
def audit_receipt(rp,v,src,obj):
 assert v['status']=='passed' and sha(src)==v['source_sha256'] and sha(obj)==v['object_sha256']
 assert '-j1' in v['command'] and '-M2048' in v['command'];assert v['timeout_seconds']==240 and v['process_group_rss_limit_bytes']==4*1024**3
 log=rp.with_suffix('.log');assert sha(log)==v['log_sha256'];a=validate(log.read_text(),v['expected_axiom_names'],v['expected_signature_names']);assert a['axiom_audits']==v['axiom_audits']
 return a
for name in sorted(names):
 src=P/'ShielddSecurity'/(name+'.lean');obj=P/'.lake/build/lib/lean/ShielddSecurity'/(name+'.olean')
 matches=[(rp,json.loads(rp.read_text())) for rp in attempts if json.loads(rp.read_text())['module']==name and json.loads(rp.read_text())['status']=='passed'];assert len(matches)==1,name
 rp,v=matches[0];a=audit_receipt(rp,v,src,obj)
 for n,item in v['frozen_imports'].items():
  if not n.startswith('ShielddSecurity.'):continue
  sp=P/(n.replace('.','/')+'.lean');op=P/'.lake/build/lib/lean'/(n.replace('.','/')+'.olean');assert sha(sp)==item['source_sha256'] and sha(op)==item['object_sha256'],n
  short=n.removeprefix('ShielddSecurity.')
  if short not in names:
   orig=packet['reused'][short];assert orig['source_sha256']==sha(sp) and orig['object_sha256']==sha(op);assert sha(R/orig['original_receipt_path'])==orig['original_receipt_sha256'];inherited[n]=dict(**orig,source_path=str(sp.relative_to(R)),credit='inherited exact source/object/receipt; zero fresh execution')
 c=v['frozen_imports']['official_import_closure'];f=O/c['manifest_file'];assert sha(f)==c['manifest_sha256'];official.add(f)
 current[name]=dict(receipt=str(rp.relative_to(R)),receipt_sha256=sha(rp),source_sha256=sha(src),object_sha256=sha(obj),audits=a['axiom_audits'])
 cost.append(dict(module=name,source_bytes=src.stat().st_size,object_bytes=obj.stat().st_size,seconds=v['seconds'],peak_group_rss_bytes=v['peak_group_rss_bytes'],audits=a['axiom_audits']))
# Attribution-only successor is a separate execution, never substitutes imports
# in the previously successful whole-call closure.
C=R/'work/mac-poseidon-width3-call10-attribution01';CO=R/'outputs/mac-poseidon-width3-call10-attribution01';name='TransferPoseidonWidth3Prefix10AbsorbProof01';src=C/'project/ShielddSecurity'/(name+'.lean');old=P/'ShielddSecurity'/(name+'.lean');obj=C/'project/.lake/build/lib/lean/ShielddSecurity'/(name+'.olean');rp=CO/('build-'+name+'-01.json');v=json.loads(rp.read_text());a=audit_receipt(rp,v,src,obj)
assert src.read_text()==old.read_text().replace('generate_absorption.py;','generate_absorption_proof.py;')
correction=dict(receipt=str(rp.relative_to(R)),receipt_sha256=sha(rp),source=str(src.relative_to(R)),source_sha256=sha(src),object_sha256=sha(obj),audits=a['axiom_audits'],change='comment header only; maintained template regenerated,10 fresh audits; original imports unchanged')
for n,item in v['frozen_imports'].items():
 if not n.startswith('ShielddSecurity.'):continue
 assert sha(C/'project'/(n.replace('.','/')+'.lean'))==item['source_sha256'];assert sha(C/'project/.lake/build/lib/lean'/(n.replace('.','/')+'.olean'))==item['object_sha256']
cost.append(dict(module=name+'-attribution-successor',source_bytes=src.stat().st_size,object_bytes=obj.stat().st_size,seconds=v['seconds'],peak_group_rss_bytes=v['peak_group_rss_bytes'],audits=a['axiom_audits']))
review=S/'review-snapshot01/manifest.json';frozen=json.loads(review.read_text())
for item in frozen['files']:assert sha(R/item['source_path'])==item['sha256'],item['source_path']
replay=R/'work/call10-repro01/outputs/mac-poseidon-width3-call10/replay-result01.json';replayed=json.loads(replay.read_text());assert replayed['status']=='passed' and len(replayed['sources'])==19
for item in replayed['sources']:
 expected=src if item['attribution_only_successor'] else P/'ShielddSecurity'/(item['module']+'.lean');assert sha(expected)==item['sha256'];assert sha(P/'ShielddSecurity'/(item['module']+'.lean'))==item['accepted_source_sha256']
for n,h in replayed['maintained_inputs'].items():assert sha(S/n)==h
assert sha(S/'verify_replay.py')==replayed['recipe_sha256'];after=snapshot();assert before==after
failures=[dict(receipt=str(rp.relative_to(R)),**{k:v.get(k) for k in ['source_sha256','exit','reason','status']},proof_credit=0) for rp in attempts if (v:=json.loads(rp.read_text()))['status']!='passed'];assert len(failures)==5,len(failures)
for fail in failures:assert any(sha(f)==fail['source_sha256'] for f in (O/'source-history').glob('*')),fail
floor=next(x for x in cost if 'ImportFloor' in x['module'])
scope='Second captured width3 domain18arity1 call: arbitrary same-final assignment hash3,238 materialized/copy steps for317 actual selected rows, exact capture38876..39191+copy200769 positions in page38400..39423+copy,476 earlier actual page rows conditionally preserved. Later232 page rows/upstream/native/fullrelationOPEN.'
summary=dict(status='passed',scope=scope,current_pass=current,attribution_successor=correction,fresh_module_executions=len(cost),fresh_unique_modules=22,fresh_axiom_audits=sum(c['audits'] for c in cost),fresh_fulltype_audits=sum(c['audits'] for c in cost),import_floor_is_cost_only=True,inherited_modules=len(inherited),inherited_fresh_execution=0,selected_rows=317,arithmetic_rows=316,copy_rows=1,materialized_steps=237,steps=238,prior_page_rows=476,page_rows=1024,page_with_copy=1025,later_page_rows=232,writes=[61614,61929],cuts='one6term LC,raw363983',domain=18,arity=1,IV=274,output=dict(raw365617_association='data only output-association01.json',mathematical='final state1 equals independent Poseidon.hash3'),controls=dict(absorption_round_rejections=9,page_selection_rejections=5,page_positive=1,semantic_inequality_claim=False),costs=cost,total_source_bytes=sum(c['source_bytes'] for c in cost),total_object_bytes=sum(c['object_bytes'] for c in cost),total_seconds=sum(c['seconds'] for c in cost),peak_group_rss_bytes=max(c['peak_group_rss_bytes'] for c in cost),import_floor=floor,RSS_note='Sampled total RSS; differences do not establish marginal heap/import attribution.',failures=failures,replay=dict(result=str(replay.relative_to(R)),sha256=sha(replay),generated_sources=19,one_attribution_only_successor=True),review_snapshot_sha256=sha(review),source_review_acceptance='Await orchestrator disposition',limits=dict(LEAN_NUM_THREADS=1,j=1,heap_MiB=2048,seconds=240,group_RSS_bytes=4*1024**3),full_transfer='OPEN',open=['Later page-row consumer preservation','Upstream input-cut evaluation','Native/runtime callsite identity and parent consumer identity','Full200770row global inclusion/partition','Clean baseline/verifier/VK correspondence','Full Transfer theorem'])
(O/'whole-call-result01.json').write_text(json.dumps(summary,indent=2)+'\n');(O/'seal-provenance01.json').write_text(json.dumps(dict(status='passed',before=before,after_equal_before=True,inherited_imports=inherited,review_snapshot_sha256=sha(review),seconds=time.monotonic()-started),indent=2)+'\n')
files=[]
def add(path,category,publish=True):
 rel=str(path.relative_to(R))
 if any(i['path']==rel for i in files):return
 files.append(dict(path=rel,category=category,publication=publish,**ident(path)))
for f in sorted(S.glob('*.py')):add(f,'maintained_generator_or_guard')
for f in sorted(S.glob('*.lean.txt')):add(f,'maintained_template')
generated={i['module'] for i in replayed['sources']}
for n in sorted(names):add(P/'ShielddSecurity'/(n+'.lean'),'generated_accepted_instance' if n in generated else 'handwritten_or_canonical_helper')
add(src,'regenerated_attribution_only_successor');add(rp,'fresh_attribution_successor_receipt');add(rp.with_suffix('.log'),'raw_observation',False)
for n in ['lakefile.lean','lake-manifest.json','lean-toolchain']:add(P/n,'package_identity')
for f in sorted(attempts):add(f,'fresh_pass_or_failure_receipt');add(f.with_suffix('.log'),'raw_observation',False)
for f in sorted(official):add(f,'official_closure_identity')
for f in sorted(O.glob('*.json')):
 if f.name.startswith(('build-','official-imports','publication-','seal-guard')):continue
 add(f,'qualified_input_or_result')
for f in sorted((O/'source-history').glob('*')):add(f,'preserved_failure_or_source_predecessor')
add(replay,'portable_replay_result');add(review,'source_review_manifest')
manifest=O/'publication-manifest01.json';assert not manifest.exists();manifest.write_text(json.dumps(dict(schema='finite-width3-whole-call10-packet-v1',scope=scope,files=files,receipts=current,attribution_successor=correction,inherited_imports=inherited,raw_logs_local_only=True,no_git_writes=True),indent=2)+'\n')
print(json.dumps(dict(status='passed',manifest=str(manifest),sha256=sha(manifest),files=len(files),fresh=len(cost),audits=summary['fresh_axiom_audits'],seconds=time.monotonic()-started)))
