from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-public-orders-endpoint-20261012-04/assemble.py').read_text()
for old,new in [
 ("CURRENT = DIAG / 'transfer-scalar-public-orders-20261012-04'","CURRENT = DIAG / 'transfer-scalar-choice-correspondence-20261012-01'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-public-orders-checkpoint-20261012-04'","CHECKPOINT = DIAG / 'transfer-scalar-choice-correspondence-checkpoint-20261012-01'"),
 ("MODULE = 'TransferScalarPublicOrders01'","MODULE = 'TransferScalarChoiceCorrespondence01'"),
 ('scalar-public-orders-endpoint01.tar.xz','scalar-choice-correspondence-endpoint01.tar.xz'),
 ('assert len(fresh) == 7','assert len(fresh) == 6'),
 ("declaration_kinds.count('def') == 0 and declaration_kinds.count('theorem') == 7","declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 5"),
 ("assert pool['objects'] == 203 and len(pool['inherited_public_reports']) == 1422","assert pool['objects'] == 207 and len(pool['inherited_public_reports']) == 1467"),
 ('fresh-7-complete-declarations.txt','fresh-6-complete-declarations.txt'),
 ('scalar_public_orders_source_shape','scalar_choice_correspondence_source_shape'),
 ('scalar-public-orders-shape.json','scalar-choice-correspondence-shape.json')]:
 assert old in s,old;s=s.replace(old,new)
old="assert len(combined_reports)==1422 and combined_reports==pool['inherited_public_reports']\nassert len(manager_selected)==203"
assert s.count(old)==1
merge="""assert len(combined_reports)==1422 and len(manager_selected)==203
dependency_packages=[]
for dirname,filename,module,count,wanted in [
 ('transfer-scalar-pow-bit-integer-endpoint-20261012-03','scalar-pow-bit-integer','TransferScalarPowBitInteger01',6,'32b7290c2eed3d3501e7824a6a8ef647d55d967fd9bffee4620d27f5501973c3'),
 ('transfer-scalar-pow-field-endpoint-20261012-08','scalar-pow-field','TransferScalarPowField01',6,'2b6c2bd99648d804315ce27ffe86696d6f3911cf0bb381d0d15504ac180bd231'),
 ('transfer-scalar-choice-masks-endpoint-20261012-06','scalar-choice-masks','TransferScalarChoiceMasks01',21,'074bf306301458f5571f6cbf57739e48354160f4bed07afae545f7460f5cea1c'),
 ('transfer-scalar-constant-equality-endpoint-20261012-04','scalar-constant-equality','TransferScalarConstantEquality01',12,'ce16a3943bbe7f4f8977234e8cd6656288ae343b1f73495615e7115246c6ebac')]:
 endpoint=DIAG/dirname;carrier=endpoint/('portable-windows-'+filename+'-endpoint01.tar.xz')
 assert pin(carrier)['sha256']==wanted
 with tarfile.open(carrier,'r:xz') as tar:
  qplan=json.loads(tar.extractfile('qualified/plan.json').read())
  qevents=[json.loads(line) for line in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
  qreview=json.loads(tar.extractfile('review.json').read())
  qpool=json.loads(tar.extractfile('context/owned-composition-review.json').read())
  qreference=json.loads(tar.extractfile('context/inherited-reference.json').read())
  report_name='reports/fresh-%d-complete-declarations.txt'%count
  qstdout=tar.extractfile(report_name).read().decode()
  qreports=m.audit(qstdout,qplan['targets'][0]['audit_names'])
  assert len(qevents)==2 and qevents[-1]['result']['status']=='passed'
  assert len(qreports)==count and qreports==qevents[-1]['result']['audits']==qreview['fresh_audits']
  assert json.loads((endpoint/'review.json').read_bytes())==qreview
  for name,report in qpool['inherited_public_reports'].items():assert combined_reports[name]==report
  known={row['module']:row for row in manager_selected}
  for row in qpool['selected']:
   assert known[row['module']]['source']==row['source'] and known[row['module']]['object']==row['object']
  assert set(combined_reports).isdisjoint(qreports);combined_reports.update(qreports)
  manager_selected.append({'module':module,'source':qplan['targets'][0]['source'],'object':qevents[-1]['result']['objects'][0]})
  dependency_packages.append({'module':module,'count':count,'archive':pin(carrier),'manifest':pin(endpoint/'manifest.json'),'review':pin(endpoint/'review.json'),'reference':qreference,'plan':qplan,'events':qevents,'report_name':report_name})
assert len(combined_reports)==1467 and combined_reports==pool['inherited_public_reports'] and len(manager_selected)==207"""
s=s.replace(old,merge)
old='    carriers = [pin(manager_archive)]'
assert s.count(old)==1
s=s.replace(old,"    carriers = [pin(manager_archive)] + [item['archive'] for item in dependency_packages]")
old='    collect_archive_refs(manager_reference)'
assert s.count(old)==1
s=s.replace(old,old+"\n    for item in dependency_packages:collect_archive_refs(item['reference'])")
at=s.index("dump(ROOT / 'inherited-reference.json', reference)")
extra="""reference['scalar_dependencies']=[{key:item[key] for key in ['module','count','archive','manifest','review','reference']} for item in dependency_packages]
reference['scope']='Complete207-module1467-report first import root: original inverse/prime and exact bit/power/masks/equality branches merged with matching shared source/object/full-report identities, no ancestor replay. Every full original sealed qualification/history archive remains referenced by exact identity.'
"""
s=s[:at]+extra+s[at:]
start=s.index("unprepared=DIAG/'transfer-scalar-public-orders-20261012-01'");end=s.index('for key,filename in [',start);s=s[:start]+s[end:]
start=s.index("row=pin(CURRENT/'prepare_recipe_from02.py')");end=s.index("add(Path(__file__), 'assemble.py'",start)
packages="""correspondenceContext=json.loads((CURRENT/'context/scalar-choice-correspondence-shape.json').read_text())
for key in ['source_choice_masks','source_constant_equality','source_pow_field','source_inverse_correctness']:
 row=correspondenceContext[key];assert row in plan['pins'] and pin(row['path'])==row
 add(row['path'],'context/original-'+Path(row['path']).name,'exact original qualified source-model association; native correspondence remains separate')
for item in dependency_packages:
 prefix='dependency-qualification/'+item['module']+'/'
 with tarfile.open(item['archive']['path'],'r:xz') as tar:
  manifest=json.loads(tar.extractfile('manifest.json').read())
  original_rows={row['archive_path']:row['original'] for row in manifest['entries']}
  selected_names=['qualified/'+name for name in ['prepare.py','prepare_recipe.py','execute_bounded.py','plan.json','review.json','source-mapping.json','events.jsonl']]
  selected_names += ['source/ShielddSecurity/'+item['module']+'.lean',item['report_name']]
  for name in selected_names:
   row=original_rows[name];path=Path(row['path']);raw=tar.extractfile(name).read()
   assert pin(path)==row and raw==path.read_bytes()
   add(path,prefix+name,'exact original successful qualification source/full types/axioms/runner and unchanged physical guards; all complete original histories linked by exact sealed archive identity')
  add(item['manifest']['path'],prefix+'manifest.json','full original archive member manifest; histories preserved in the referenced full original archive')
  add(item['review']['path'],prefix+'review.json','full exact original qualification review')
"""
s=s[:start]+packages+s[end:]
s=s.replace("'rejected_attempts': 2, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 1","'rejected_attempts': 0, 'withdrawn_unrun_sources': 0, 'unprepared_setup_failures': 0")
start=s.index("    'scope': mapping['scope'] + '");end=s.index("}\ndump(ROOT / 'review.json'",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete declarations:one definition/five theorems. Exact original207-module1467-report dependency union, original successful qualification sources/types/axioms/guards and full original archive/history identities retained. No ancestor replay or native result inferred from hashes.'"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-choice-correspondence-checkpoint-20261012-01';checkpoint.mkdir()
shutil.copyfile(DIAG/'transfer-scalar-inverse-correctness-checkpoint-20261012-04/preservation_check.py',checkpoint/'preservation_check.py')
print({'complete_dependency_modules':207,'inherited_reports':1467,'fresh_declarations':6,'original_four_dependency_qualifications_and_archive_histories_preserved':True,'assembly_not_run':True})
