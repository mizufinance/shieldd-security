"""Seal numerical primality only; raw observations and compiler objects stay local."""
import hashlib,json,subprocess,time
from pathlib import Path
from audit_log import validate
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-subgroup-prime06';P=S/'project'
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as stream:
  while block:=stream.read(1024**2):h.update(block)
 return h.hexdigest()
def identity(path):return dict(bytes=path.stat().st_size,sha256=sha(path))
def snapshot():
 candidate=S/'candidate.json';assert sha(candidate)=='905fb641efe1b86350c7d5a801741cdee2d368401c58712c751f8de5781d5150'
 parent=R/'work/parent-subgroup-prime-candidate01';manifest=parent/'manifest.json'
 assert sha(manifest)=='32938d68961e6b0281e08f11f34e8a51e4b359dc398a860434047dfd592ad673'
 data=json.loads(manifest.read_text())
 for item in data['files']:assert identity(parent/item['path'])==dict(bytes=item['bytes'],sha256=item['sha256'])
 assert sha(parent/'candidate.json')==sha(candidate)
 packet=json.loads((O/'input-packet01.json').read_text())['packet']
 for key,item in packet['files'].items():
  assert sha(R/item['source_path'])==item['sha256']
  assert sha(P/'ShielddSecurity'/Path(key).name)==item['sha256']
 scalar=json.loads((O/'scalar-input01.json').read_text())
 assert sha(R/scalar['path'])==sha(R/scalar['canonical_path'])==scalar['sha256']
 assert sha(P/'ShielddSecurity/Scalar.lean')=='f0ca7c1535b7169d11be9aa77ecb08d01d9c466358d0fc29e806dbad8b1f3e01'
 return dict(candidate_sha256=sha(candidate),parent_manifest_sha256=sha(manifest),parent_files=data['files'],
   owned_dependency_packet=packet,scalar=scalar,package={n:sha(P/n) for n in ['lakefile.lean','lake-manifest.json','lean-toolchain']},
   source_acl2_certificate_sha256=json.loads(candidate.read_text())['source_certificate_sha256'])
started=time.monotonic();before=snapshot();packet=before['owned_dependency_packet']
dependencies=packet['topological_import_order']+['Scalar']
new=[f'SubgroupPrimeNode{i:02d}' for i in range(1,38)]
aux=['SubgroupPrimeInheritedAudit06','SubgroupPrimeImportFloor06','SubgroupPrimeControls06','SubgroupPrimeCarmichael06','SubgroupOrderPrime06','SubgroupPrimeConclusionFloor06']
modules=dependencies+new+aux;assert len(modules)==len(set(modules))==60
generated=new+aux[:4];handwritten=aux[4:]
receipts={};costs=[];official=set();inherited={};fresh=[]
for name in modules:
 source=P/'ShielddSecurity'/(name+'.lean');obj=P/'.lake/build/lib/lean/ShielddSecurity'/(name+'.olean')
 matches=[]
 for path in sorted(O.glob('build-'+name+'-*.json')):
  result=json.loads(path.read_text())
  if result['status']=='passed' and result['source_sha256']==sha(source) and result['object_sha256']==sha(obj):matches.append((path,result))
 assert matches,'unqualified source/object '+name
 path,result=matches[-1];assert result['command'][-1]==str(source)
 assert result['lean_heap_limit_MiB']==2048 and '-M2048' in result['command'] and '-j1' in result['command']
 assert result['timeout_seconds']==240 and result['process_group_rss_limit_bytes']==4*1024**3
 log=path.with_suffix('.log');assert sha(log)==result['log_sha256']
 audit=validate(log.read_text(),result['expected_axiom_names'],result['expected_signature_names'])
 assert audit['axiom_audits']==result['axiom_audits']
 assert audit['full_signature_sha256']==result['full_signature_sha256']
 for importName,item in result['frozen_imports'].items():
  if not importName.startswith('ShielddSecurity.'):continue
  sp=P/(importName.replace('.','/')+'.lean');op=P/'.lake/build/lib/lean'/(importName.replace('.','/')+'.olean')
  assert sha(sp)==item['source_sha256'] and sha(op)==item['object_sha256']
  if importName.removeprefix('ShielddSecurity.') not in modules:
   short=importName.removeprefix('ShielddSecurity.');rps=[]
   for prior in O.glob('build-'+short+'-00.json'):
    priorResult=json.loads(prior.read_text())
    if priorResult['status']=='passed' and priorResult['source_sha256']==sha(sp) and priorResult['object_sha256']==sha(op):rps.append((prior,priorResult))
   assert rps,'unqualified inherited import '+importName
   prior,priorResult=rps[-1];origin=priorResult['reused_from_exact_pass_receipt']
   assert sha(R/origin['path'])==origin['sha256']
   canonical=R/'work/shared-build-handoff/circuits'/sp.relative_to(P);assert sha(canonical)==sha(sp)
   value=dict(**item,canonical_source=str(canonical.relative_to(R)),receipt=str(prior.relative_to(R)),receipt_sha256=sha(prior),
       original_receipt=origin,credit='inherited unchanged object, no fresh replay')
   if importName in inherited:assert inherited[importName]==value
   inherited[importName]=value
 external=result['frozen_imports']['official_import_closure'];manifest=O/external['manifest_file']
 assert sha(manifest)==external['manifest_sha256'];official.add(manifest)
 receipts[name]=dict(path=str(path.relative_to(R)),sha256=sha(path),audits=result['axiom_audits'])
 costs.append(dict(module=name,source_bytes=source.stat().st_size,object_bytes=obj.stat().st_size,seconds=result['seconds'],
      peak_group_rss_bytes=result['peak_group_rss_bytes'],audits=result['axiom_audits'],full_type_audits=len(result['expected_signature_names']),heap_MiB=result['lean_heap_limit_MiB']))
 fresh.extend(O.glob('build-'+name+'-*.json'))
officialFiles={};revisions={}
for path in sorted(official):
 data=json.loads(path.read_text())
 for key,h in data['files'].items():
  if key in officialFiles:assert officialFiles[key]==h
  officialFiles[key]=h
 for package,revision in data['revisions'].items():
  if package in revisions:assert revisions[package]==revision
  revisions[package]=revision
def check_official():
 for package,revision in revisions.items():
  root=P/'.lake/packages'/package
  assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==revision
  assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=root,text=True).strip()
 for key,h in officialFiles.items():
  package,relative=key.split('/',1)
  root=Path.home()/'.elan/toolchains/leanprover--lean4---v4.30.0' if package=='lean4' else P/'.lake/packages'/package
  assert sha(root/relative)==h,'official source/object mutation '+key
 return hashlib.sha256(json.dumps(officialFiles,sort_keys=True).encode()).hexdigest()
officialBefore=check_official()
expected={n:sha(P/'ShielddSecurity'/(n+'.lean')) for n in generated}
for script in ['generate_subgroup_primes.py','generate_controls.py']:
 subprocess.run(['python3',str(S/script)],cwd=R,check=True,stdout=subprocess.DEVNULL)
assert expected=={n:sha(P/'ShielddSecurity'/(n+'.lean')) for n in generated}
after=snapshot();assert before==after;assert check_official()==officialBefore
floor=next(x for x in costs if x['module']=='SubgroupPrimeConclusionFloor06')
root=next(x for x in costs if x['module']=='SubgroupPrimeNode37')
core=[x for x in costs if x['module'] in new]
failures=[]
for path in sorted(set(fresh)):
 r=json.loads(path.read_text())
 if r['status']!='passed':failures.append(dict(path=str(path.relative_to(R)),status=r['status'],source_sha256=r['source_sha256'],
     exit=r.get('exit'),reason=r.get('reason'),proof_credit=0))
scope='Nat.Prime exact Jubjub subgroup-order integer and canonical Scalar.order; 51 recursive Lucas nodes, 37 new and 14 reused-source prime nodes freshly compiled'
summary=dict(schema='bounded-subgroup-order-primality-v1',status='passed',scope=scope,
 order=json.loads((S/'candidate.json').read_text())['subgroup_order'],new_nodes=37,common_field_prime_nodes=14,
 fresh_modules=len(modules),fresh_audits=sum(x['audits'] for x in costs),fresh_full_type_audits=sum(x['full_type_audits'] for x in costs),new_certificate_audits=74,
 canonical_conclusion='ShielddSecurity.SubgroupOrderPrime06.order_prime : Nat.Prime ShielddSecurity.Scalar.order',
 limits=dict(lean_threads=1,heap_MiB=2048,rss_bytes=4*1024**3,seconds_per_module=240,free_memory_percent=15,free_disk_bytes=2*1024**3),
 module_costs=costs,root=root,import_floor=floor,core_source_bytes=sum(x['source_bytes'] for x in core),
 core_object_bytes=sum(x['object_bytes'] for x in core),core_build_seconds=sum(x['seconds'] for x in core),
 all_build_seconds=sum(x['seconds'] for x in costs),peak_group_rss_bytes=max(x['peak_group_rss_bytes'] for x in costs),
 RSS_minus_conclusion_import_floor={x['module']:x['peak_group_rss_bytes']-floor['peak_group_rss_bytes'] for x in costs},
 RSS_note='sampled total process-group RSS; differences are observations without causal import-floor attribution',
 controls=dict(positive_root=True,root_rejected=['base1','one residue+1 modulo n','one exponent+1','one omitted factor'],
    residue_mutation_ran=True,Carmichael561=dict(arithmetic_check=True,child_primality=False,root_primality=False),
    type_errors_timeouts_and_cache_credit=0),failures=failures,
 preflights=['dependency-preflight01.json','node-launch-preflight01.json'],cache_retrieval=dict(receipt='cache-guard01.json',proof_credit=0),
 open=['actual Mathlib curve point order/cardinality','Hasse bound and group-law/cardinality join','native SpendAuth generator/codec identity',
       'global parent relation inclusion','clean-source verifier/VK correspondence','full Transfer theorem'],full_transfer='OPEN')
assert summary['fresh_audits']==133 and summary['fresh_full_type_audits']==122
(O/'subgroup-prime-result01.json').write_text(json.dumps(summary,indent=2)+'\n')
(O/'seal-provenance01.json').write_text(json.dumps(dict(status='passed',before=before,after_equal_before=True,
      generated_sources_equal=True,generated_module_count=len(generated),official_files=len(officialFiles),
      official_files_digest=officialBefore,official_before_after_equal=True,scope=scope,seconds=time.monotonic()-started),indent=2)+'\n')
files=[]
def add(path,category,publish=True):
 key=str(path.relative_to(R))
 if any(x['path']==key for x in files):return
 files.append(dict(path=key,category=category,publication=publish,**identity(path)))
for p in sorted(S.glob('*.py')):add(p,'handwritten_generator_or_guard')
for p in sorted(S.glob('*.lean.txt')):add(p,'handwritten_control_template')
for p in [S/'candidate.json',S/'inherited-prime-map01.json']:add(p,'qualified_candidate_data_or_source_map')
for n in modules:add(P/'ShielddSecurity'/(n+'.lean'),
   'generated_prime_or_audit_or_control' if n in generated else ('handwritten_conclusion_or_floor' if n in handwritten else 'canonical_dependency_fresh_build'),n not in dependencies)
for n in ['lakefile.lean','lake-manifest.json','lean-toolchain']:add(P/n,'frozen_package_identity')
for p in sorted(set(fresh)):
 add(p,'fresh_pass_or_failure_receipt');add(p.with_suffix('.log'),'raw_observation_local_only',False)
for value in inherited.values():add(R/value['receipt'],'inherited_import_qualification_reference')
for p in sorted(official):add(p,'deduplicated_official_import_closure')
for p in sorted(O.glob('*.json')):
 if p.name.startswith(('publication-','build-','official-imports','seal-guard')):continue
 add(p,'qualified_metadata_or_data_or_preflight')
for p in sorted(O.glob('cache-guard*.log')):add(p,'raw_observation_local_only',False)
for p in sorted(O.glob('seal-guard*.json')):
 add(p,'preserved_seal_guard_failure_zero_credit');add(p.with_suffix('.log'),'raw_observation_local_only',False)
for p in sorted((O/'source-history').glob('*')):
 if p.is_file():add(p,'preserved_predecessor_zero_proof_credit')
assert len(files)==len({x['path'] for x in files})
manifest=dict(schema='finite-subgroup-order-prime-publication-v1',files=files,current_pass_receipts=receipts,
 fresh_common_source_replay=True,inherited_imports=inherited,raw_logs='local only; active seal guard bound by post-run envelope',
 official_cache_objects_and_oleans_not_published=True,parent_candidate_manifest_sha256=before['parent_manifest_sha256'],
 numeric_claim=scope,full_transfer='OPEN')
dest=O/'publication-manifest01.json';assert not dest.exists();dest.write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(status='passed',manifest_sha256=sha(dest),files=len(files),publication_files=sum(x['publication'] for x in files),
 modules=len(modules),audits=summary['fresh_audits'],core_source_bytes=summary['core_source_bytes'],core_object_bytes=summary['core_object_bytes'],
 core_build_seconds=summary['core_build_seconds'],seconds=time.monotonic()-started)),flush=True)
