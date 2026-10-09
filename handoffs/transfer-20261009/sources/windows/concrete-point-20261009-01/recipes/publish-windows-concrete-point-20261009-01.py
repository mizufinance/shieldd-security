from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess,sys
repo=Path('C:/src/shieldd-transfer-windows-publication-20261009');local=Path('C:/src/shieldd-transfer-handoffs');diag=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
base=repo/'handoffs/transfer-20261009';dest=base/'sources/windows/concrete-point-20261009-01';parent='d90ffc4950623e68ed64d6d0200ea0f5d93da9ec'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def write(p,v):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((json.dumps(v,indent=2)+'\n').encode())
def git(*args):return subprocess.check_output(['git','-c','core.longpaths=true','-C',str(repo),*args],text=True).strip()
runs=[('windows-concrete-edwards-20261009-01','safe-concrete-edwards-boundary-2026100901',14),('windows-point-smoke-20261009-03','safe-point-smoke-boundary-2026100903',6),('windows-concrete-point-20261009-05','safe-concrete-point-boundary-2026100905',None)]
phase=sys.argv[1]
if phase=='sources':
 assert not dest.exists();dest.mkdir(parents=True);files={};resolution={}
 def copy(p,rel):
  target=dest/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(p.read_bytes());files[rel]={'sha256':sha(target),'bytes':target.stat().st_size}
 for stem,boundary,count in runs:
  m=load(diag/(stem+'-source/manifest.json'));copy(diag/(stem+'-source/manifest.json'),'inputs/'+stem+'.json')
  for name,item in m['sources'].items():
   p=repo/'circuits/ShielddSecurity'/(name+'.lean');assert sha(p)==item['sha256'];copy(p,'circuits/ShielddSecurity/'+p.name)
  recipe='prepare-windows-concrete-edwards-20261009-01.py' if 'concrete-edwards' in stem else ('prepare-point-smoke-20261009-03.py' if 'smoke' in stem else 'prepare-concrete-point-20261009-05.py')
  for p in [local/recipe,local/('run-safe-'+stem+'.ps1'),diag/('root-'+stem+'.ps1'),diag/('audit-'+stem+'.py')]:copy(p,'recipes/'+p.name)
  identities={name:v['sha256'] for name,v in m['sources'].items()};identities.update({v['name']:v['original_source_sha256'] for v in m['reused']})
  for name,digest in identities.items():
   candidates=[repo/'circuits/ShielddSecurity'/(name+'.lean')]
   if not any(p.exists() and sha(p)==digest for p in candidates):candidates=list((base/'sources/windows').rglob(name+'.lean'))
   matches=[p for p in candidates if p.exists() and sha(p)==digest];assert matches,(name,digest)
   resolution[name]={'path':matches[0].relative_to(repo).as_posix(),'sha256':digest}
 recipes=['prepare-windows-concrete-edwards-20261009-01.py','prepare-concrete-edwards-pilot-20261009-01.py','inspect-field-concrete-closure-20261009-01.py','inspect-concrete-edwards-closure-20261009-01.py','compose-concrete-edwards-cache-20261009-01.py','inspect-edwards-point-closure-20261009-01.py','report-point-import-floor-20261009-01.py','report-edwards-inspection-path-disposition-20261009-01.py','PointCacheHashCatalog01.lean','inspect-point-official-artifacts-20261009-01.py','inspect-point-official-artifacts-20261009-02.py','fetch-point-official-artifacts-20261009-01.py','fetch-point-official-artifacts-20261009-02.py','stop-point-owned-fetch-20261009-02.py','prepare-point-fetch-successor-20261009-02.py','copy-point-qualified-artifacts-20261009-01.py','copy-point-qualified-artifacts-20261009-02.py','compose-point-smoke-cache-20261009-01.py','compose-concrete-point-cache-20261009-01.py','inspect-concrete-point-closure-20261009-01.py']
 for name in recipes:copy(local/name,'recipes/'+name)
 for p in [local/'prepare-point-smoke-20261009-01.py',diag/'root-windows-point-smoke-20261009-01.ps1',diag/'audit-windows-point-smoke-20261009-01.py',local/'run-safe-windows-point-smoke-20261009-01.ps1',diag/'windows-point-smoke-20261009-01-source/manifest.json',diag/'windows-point-smoke-20261009-01-source/MathlibPointImportSmoke01.lean']:
  copy(p,'failed/smoke01/'+p.name)
 for label in ['01','02','03']:copy(local/('compose-point-smoke-cache-20261009-'+label+'-recovered.py'),'recipes/compose-point-smoke-cache-20261009-'+label+'-recovered.py')
 copy(local/'compose-point-smoke-cache-20261009-03-original.py','recipes/compose-point-smoke-cache-20261009-03-original.py')
 copy(local/'report-point-composer-path-disposition-20261009-02.py','recipes/report-point-composer-path-disposition-20261009-02.py')
 copy(local/'point-composer-path-disposition-20261009-02.json','data/point-composer-path-disposition-20261009-02.json')
 copy(local/'prepare-point-smoke-successor-20261009-03.py','recipes/prepare-point-smoke-successor-20261009-03.py')
 for p in [local/'prepare-point-smoke-20261009-02.py',diag/'root-windows-point-smoke-20261009-02.ps1',diag/'audit-windows-point-smoke-20261009-02.py',local/'run-safe-windows-point-smoke-20261009-02.ps1',diag/'windows-point-smoke-20261009-02-source/manifest.json',diag/'windows-point-smoke-20261009-02-source/MathlibPointImportSmoke01.lean']:
  copy(p,'failed/smoke02/'+p.name)
 for p in [local/'prepare-concrete-point-20261009-01.py',diag/'root-windows-concrete-point-20261009-01.ps1',diag/'audit-windows-concrete-point-20261009-01.py',local/'run-safe-windows-concrete-point-20261009-01.ps1',diag/'windows-concrete-point-20261009-01-source/manifest.json',diag/'windows-concrete-point-20261009-01-source/ConcreteWeierstrassPoint01.lean']:
  copy(p,'failed/point01/'+p.name)
 for p in [local/'inspect-concrete-point-closure-20261009-05.py',local/'compose-concrete-point-cache-20261009-05.py']:copy(p,'recipes/'+p.name)
 copy(local/'prepare-concrete-point-20261009-02.py','failed/point02/prepare-concrete-point-20261009-02.py')
 copy(local/'prepare-concrete-point-20261009-03.py','failed/point03/prepare-concrete-point-20261009-03.py')
 for p in [local/'prepare-concrete-point-20261009-04.py',local/'compose-concrete-point-cache-20261009-04.py',diag/'root-windows-concrete-point-20261009-04.ps1',local/'run-safe-windows-concrete-point-20261009-04.ps1']:copy(p,'failed/point04/'+p.name)
 for label in ['01','02']:
  for p in [diag/('root-windows-point-cache-20261009-'+label+'.ps1'),local/('run-safe-windows-point-cache-20261009-'+label+'.ps1')]:copy(p,'recipes/'+p.name)
 for name in ['point-import-floor-report-20261009-01.json','edwards-inspection-path-disposition-20261009-01.json','point-official-artifact-inspection-20261009-02.json']:copy(local/name,'data/'+name)
 for name in ['concrete-edwards-closure-inspection-20261009-01.json','edwards-point-closure-inspection-20261009-01.json','concrete-point-closure-inspection-20261009-01.json','concrete-point-closure-inspection-20261009-05.json']:
  data=load(local/name);summary={'kind':'Compact transport of read-only closure inspection; full local original preserved','original_inspection_sha256':sha(local/name),'source_sha256_by_module':{k:v['sha256'] for k,v in data['sources'].items()},'present_artifact_files':len(data['files']),'present_artifact_bytes':data['bytes'],'missing_artifact_files':len(data['missing']),'proof_credit':0}
  p=dest/'data'/name.replace('.json','-summary.json');write(p,summary);files[p.relative_to(dest).as_posix()]={'sha256':sha(p),'bytes':p.stat().st_size}
 copy(local/'point-artifact-stage-20261009-02/receipt.json','data/qualified-point-artifacts-20261009-02.json')
 copy(local/'point-qualified-companions-20261009-02/manifest.json','data/qualified-point-copy-20261009-02.json')
 copy(Path(__file__),'recipes/'+Path(__file__).name)
 write(dest/'dependency-resolution.json',resolution);files['dependency-resolution.json']={'sha256':sha(dest/'dependency-resolution.json'),'bytes':(dest/'dependency-resolution.json').stat().st_size}
 write(dest/'manifest.json',{'files':files,'parent_commit':parent,'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','scope':'Concrete parameter and discriminant proofs; separately guarded Mathlib Point import and concrete point-set join. Actual outcomes recorded only in receipt.','Mathlib_Point_join':'PENDING_ACTUAL_RECEIPT','addition':'OPEN','StandardCurveModel':'OPEN','cardinality':'OPEN','curve_order':'OPEN','native_representation':'OPEN','full_transfer':'OPEN'})
 print(json.dumps({'files':len(files),'closure':len(resolution),'manifest_sha256':sha(dest/'manifest.json')}))
elif phase=='verify-index':
 for rel,item in load(dest/'manifest.json')['files'].items():
  path=(dest/rel).relative_to(repo).as_posix();assert hashlib.sha256(subprocess.check_output(['git','-C',str(repo),'show',':'+path])).hexdigest()==item['sha256'],path
 for p in (dest/'circuits/ShielddSecurity').glob('*.lean'):assert hashlib.sha256(subprocess.check_output(['git','-C',str(repo),'show',':circuits/ShielddSecurity/'+p.name])).hexdigest()==sha(p)
 print('Exact source Git index bytes PASS')
elif phase=='receipts':
 outcomes={};total=0
 for stem,boundary,count in runs:
  k=diag/(stem+'-kernel');b=diag/boundary;m=load(diag/(stem+'-source/manifest.json'));modules={}
  assert (b/'end.txt').exists() and (b/'resume-status.txt').read_text().strip()=='0'
  success=(k/'complete.txt').exists() and (k/'end.txt').exists() and (k/'exit.txt').read_text().strip()=='0'
  if success:
   for name in m['order']:
    leaf=k/name;a=load(leaf/'audit.json');assert a['full_types_checked'] and sha(k/'project'/m['sources'][name]['lean_relative_path'])==m['audited_candidates'][name]==a['candidate_sha256']
    assert (leaf/'exit.txt').read_text().strip()=='0' and (leaf/'end.txt').exists() and not (leaf/'stop.txt').exists()
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in a['axioms'].values())
    modules[name]={'audit':a,'actual_exit':0,'stdout_sha256':sha(leaf/'stdout.txt'),'stderr_sha256':sha(leaf/'stderr.txt')}
   n=sum(v['audit']['audits'] for v in modules.values());assert count is None or n==count;total+=n
   outcomes[stem]={'success':True,'modules':modules,'declaration_audits':n,'manifest_sha256':sha(k/'manifest.json'),'recipe':load(k/'recipe.json'),'actual_exit':0,'root_resume_status':0,'start':(k/'start.txt').read_text().strip(),'end':(k/'end.txt').read_text().strip(),'qualified_reused_modules':m['reused'],'external_overlay':load(k/'external-overlay.json'),'external_before_sha256':sha(k/'external-before.json'),'external_identity_rechecked':True}
  else:
   outcomes[stem]={'success':False,'proof_and_control_credit':0,'source_manifest_sha256':sha(diag/(stem+'-source/manifest.json')),'root_resume_status':0,'failure':(k/'failure.txt').read_text() if (k/'failure.txt').exists() else (b/'failure.txt').read_text(),'actual_exit':1}
 assert outcomes[runs[0][0]]['success']
 artifact=load(local/'point-artifact-stage-20261009-02/receipt.json');b=diag/'safe-point-cache-boundary-2026100902';assert (b/'complete.txt').exists() and (b/'resume-status.txt').read_text().strip()=='0'
 failedsmoke=diag/'windows-point-smoke-20261009-01-kernel';failedboundary=diag/'safe-point-smoke-boundary-2026100901';assert (failedsmoke/'exit.txt').read_text().strip()=='1' and (failedboundary/'resume-status.txt').read_text().strip()=='0'
 join=outcomes[runs[2][0]]['success'];smoke=outcomes[runs[1][0]]['success']
 receipt={'runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','mathlib_sha':'c5ea00351c28e24afc9f0f84379aa41082b1188f','lean_version':'4.30.0','parent_commit':parent,'source_commit':git('rev-parse','HEAD'),'source_packet_manifest_sha256':sha(dest/'manifest.json'),'source_index_exact_bytes_verified':True,'source_diff_check_exit':int(sys.argv[2]),'source_diff_check_disposition':'Frozen producer bytes preserved, including CRLF/EOF whitespace; receipt checked separately','runs':outcomes,'declaration_audits':total,'fresh_local_modules':sum(len(v.get('modules',{})) for v in outcomes.values()),'cached_foreign_declaration_audits':4 if smoke else 0,'new_negative_control_credit':0,'Point_original_1GiB_preflight':{'run':False,'proof_credit':0,'report_sha256':sha(local/'point-import-floor-report-20261009-01.json')},'Point_separate_2GiB_artifact_qualification':{'success':True,'proof_credit':0,'cap_bytes':2*1024**3,'bytes':artifact['final_qualified_closure_bytes'],'receipt_sha256':sha(local/'point-artifact-stage-20261009-02/receipt.json'),'root_resume_status':0},'artifact_preparation_failures':{'fetch01':'WSL process already led its group; EPERM before artifact retrieval','copy01':'Incorrect PowerShell executable path before any companion copy','proof_and_control_credit':0},'inspection_path_metadata_disposition':{'report_sha256':sha(local/'edwards-inspection-path-disposition-20261009-01.json'),'proof_credit':0,'sealed_sources_objects_audits_unchanged':True},'concrete_parameters':'PROVED','displayed_discriminant_nonzero':'PROVED','Point_import_smoke':'PASS' if smoke else 'BOUNDED_FAILURE','Mathlib_discriminant_and_ellipticity':'PROVED' if join else 'OPEN','Mathlib_full_point_set_equivalence':'PROVED' if join else 'OPEN','exceptional_identity_and_torsion_images':'PROVED' if join else 'OPEN','addition_homomorphism':'OPEN','StandardCurveModel':'OPEN','cardinality':'OPEN','global_curve_order':'OPEN','native_representation':'OPEN','full_transfer':'OPEN'}
 receipt['failed_smoke01']={'proof_and_control_credit':0,'actual_exit':1,'root_resume_status':0,'reason':'Wrappers omitted the DecidableEq F premise required by the Point group instance; corrected source in fresh smoke02','stdout_sha256':sha(failedsmoke/'MathlibPointImportSmoke01/stdout.txt'),'stderr_sha256':sha(failedsmoke/'MathlibPointImportSmoke01/stderr.txt'),'source_manifest_sha256':sha(diag/'windows-point-smoke-20261009-01-source/manifest.json')}
 failedsmoke02=diag/'windows-point-smoke-20261009-02-kernel';assert (failedsmoke02/'MathlibPointImportSmoke01/exit.txt').read_text().strip()=='0' and (failedsmoke02/'exit.txt').read_text().strip()=='1' and (diag/'safe-point-smoke-boundary-2026100902/resume-status.txt').read_text().strip()=='0'
 receipt['failed_smoke02']={'proof_and_control_credit':0,'kernel_exit':0,'actual_batch_exit':1,'root_resume_status':0,'reason':'Audit parser did not accept printed universe suffixes; corrected producer and fresh smoke03 rerun','stdout_sha256':sha(failedsmoke02/'MathlibPointImportSmoke01/stdout.txt'),'source_manifest_sha256':sha(diag/'windows-point-smoke-20261009-02-source/manifest.json')}
 failedpoint=diag/'windows-concrete-point-20261009-01-kernel';assert (failedpoint/'exit.txt').read_text().strip()=='1' and (diag/'safe-concrete-point-boundary-2026100901/resume-status.txt').read_text().strip()=='0'
 receipt['failed_point01']={'proof_and_control_credit':0,'actual_exit':1,'root_resume_status':0,'reason':'Equation equivalence simplifier omitted pow_zero and one_mul; corrected source in fresh point02. Compiler error and compiler-inserted sorryAx are not proof or control credit.','stdout_sha256':sha(failedpoint/'ConcreteWeierstrassPoint01/stdout.txt'),'source_manifest_sha256':sha(diag/'windows-concrete-point-20261009-01-source/manifest.json')}
 receipt['failed_point02_preparation']={'proof_and_control_credit':0,'kernel_run':False,'reason':'Successor builder retained the original inspection output suffix; fresh-output assertion rejected it before a new guard or Lean job existed. Corrected all namespace suffixes in fresh point03. Original inspection JSON preserved.','producer_sha256':sha(local/'prepare-concrete-point-20261009-02.py')}
 receipt['failed_point03_preparation']={'proof_and_control_credit':0,'kernel_run':False,'reason':'Successor still retained literal inspection-namespace suffix; fresh-output assertion rejected it before any guard or Lean job. All output paths corrected in point04. Original inspection JSON preserved.','producer_sha256':sha(local/'prepare-concrete-point-20261009-03.py')}
 assert (diag/'safe-concrete-point-boundary-2026100904/resume-status.txt').read_text().strip()=='0'
 receipt['failed_point04_composition']={'proof_and_control_credit':0,'kernel_run':False,'root_resume_status':0,'reason':'Composer inherited current smoke03 stage identifier from shared recipe filename01; exact-stage assertion rejected it before Lean. Correct stage substitution in fresh point05.','producer_sha256':sha(local/'prepare-concrete-point-20261009-04.py')}
 receipt['point_composer_path_disposition']={'report_sha256':sha(local/'point-composer-path-disposition-20261009-02.json'),'proof_credit':0,'successful_smoke03_producer_unchanged':True,'failed_smoke01_02_producer_bytes_recovered_exactly':True}
 receipt['concrete_Mathlib_negation_transport']='OPEN'
 receipt['pinned_Point_audit_premises']={'Point.mk_and_pointEquiv':['CommRing R','Nontrivial R','W.IsElliptic','affine equation for finite constructor'],'Point.neg':['CommRing R','Point stores nonsingularity'],'Point.instAddCommGroup':['Field F','DecidableEq F'],'concrete_ellipticity_disposition':'Derived from exact official discriminant equality and proved nonzero concrete discriminant; not an added assumption'}
 receipt['audit_scope']='Every named theorem and def in the three fresh local modules (26 local declarations on success), plus four selected pinned cached Mathlib declarations. Unnamed instance construction is covered by the audited curve_elliptic theorem; no all-Mathlib-declarations or fresh Mathlib replay claim.'
 p=base/'receipts/windows/concrete-point-20261009-01.json';assert not p.exists();write(p,receipt)
 invpath=base/'reviews/windows-semantic-family-inventory-20261009-01.json';inv=load(invpath);inv['checked_concrete_point_route']={'receipt':p.relative_to(repo).as_posix(),'sha256':sha(p),'concrete_parameters':'PROVED','Mathlib_full_point_set_equivalence':receipt['Mathlib_full_point_set_equivalence'],'addition_homomorphism':'OPEN','StandardCurveModel':'OPEN','global_curve_order':'OPEN','native_representation':'OPEN'};write(invpath,inv)
 statuspath=base/'status/windows.json';status=load(statuspath);journal=load(diag/'root-dh-primary-joint-after-initialization-2516-successor-3130/journal.json');status['snapshot_utc']=datetime.now(timezone.utc).isoformat();status['synchronized_origin_sha']=parent;status['active_controller'].update({'settled_dh_phases':len(journal),'settled_dh_modules':sum(v.get('modules',0) for v in journal),'settled_dh_audits':sum(v.get('exports',0) for v in journal),'whole_root_complete':(diag/'root-field-native-epk-cast-repair-3130/complete.txt').exists()});status['concrete_point_20261009_01']={'source_commit':receipt['source_commit'],'receipt':p.relative_to(base).as_posix(),'sha256':sha(p),'declaration_audits':total,'Mathlib_full_point_set_equivalence':receipt['Mathlib_full_point_set_equivalence'],'full_transfer':'OPEN'};write(statuspath,status)
 print(json.dumps({'receipt_sha256':sha(p),'audits':total,'Point_join':join,'settled_dh_phases':len(journal)}))
else:raise ValueError(phase)
