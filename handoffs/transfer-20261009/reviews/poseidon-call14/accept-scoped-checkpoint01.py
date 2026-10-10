"""Parent disposition from independently checked original receipts and actual reviews."""
from pathlib import Path
import ast,datetime,hashlib,json,math,sys
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
V=Path(__file__).resolve().parent;P=V.parent;C=P/'final-two-control-candidate06';F=P/'final-two-result06'
load=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
record=lambda p:dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p))
for n in [2,3]:
 for p,h in load(V/f'review-inputs0{n}.json').items():assert sha(p)==h
 d=load(V/f'opus55-final-call14-review0{n}.json');assert d['is_error'] is False and 'claude-opus-5-5' in d['modelUsage']
manifest=load(F/'final-result-manifest06.json');assert sha(F/'final-result-manifest06.json')=='a1860ff75f5117b55d5366c5aa96e0a1358830df831118fb0469065f35bbb995'
portable=load(V/'portable-actual-result01.json');rows={r['expected_ordinal']:r for r in portable['actual_receipts']};imports={};seen=[]
assert set(rows)==set(range(1,61))
for k,e in manifest['entries'].items():
 assert record(Path(e['path']))==e
 if not k.startswith('raw-local-only/') or not k.endswith('.json'):continue
 p=Path(e['path']);r=load(p);n=r['expected_ordinal'];seen.append(n);q=rows[n]
 assert q['actual_receipt_identity']==record(p)
 for key,value in q.items():
  if key in ['actual_receipt_identity','local_raw_stdout_policy']:continue
  assert key in r and r[key]==value,(n,key)
 for name,value in r.get('frozen_imports',{}).items():
  h=hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()
  imports.setdefault(h,dict(import_=name,original_record=value))
assert sorted(seen)==list(range(1,61)) and len(imports)==182
expected={h:{'import':v['import_'],'original_record':v['original_record']} for h,v in imports.items()}
assert expected==portable['qualified_import_records_deduplicated_by_exact_JSON_identity']
obs=load(F/'final60-observation06.json')
assert all(obs[k]==v for k,v in portable['observed_fields'].items())
passed=[r for r in rows.values() if r['status']=='passed']
assert len(passed)==57 and sum(r['axiom_audits'] for r in passed)==398
assert [n for n in sorted(rows) if rows[n]['status']!='passed']==[55,56,58]
assert all(rows[n]['fresh_credit']==0 and rows[n]['exit']==1 for n in [55,56,58])
parent=load(V/'parent-final-RAW-inspection01.json');assert parent['accepted_audits']==398 and parent['original60_remaining']==0 and parent['parent_new_Lean_runs']==0
si=load(C/'source-inventory06.json');ctx=load(C/'continuation-context06.json')
helper=C/'maintained/continuation_context.py';inventory=load(C/'maintained-inventory06.json')
assert sha(helper)==inventory['maintained_files']['continuation_context.py']['sha256']
# Execute only the four inspected pure census definitions, no campaign entrypoint.
tree=ast.parse(helper.read_text());names={'charged_files','runtime_metadata_size','charged_total','aggregate_budget'}
selected=ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in names],type_ignores=[])
assert len(selected.body)==4
env=dict(Path=Path,json=json,math=math,sha=sha,FUTURE=['TransferPoseidonCall14Proof01','TransferPoseidonCall14CheckedControls01'])
exec(compile(selected,str(helper),'exec'),env)
budget=env['aggregate_budget'](ctx,parent['final_state'],Path(si['execution_paths']['output_dir']))
md=env['runtime_metadata_size'](ctx)
assert budget['attempts']==60 and abs(budget['seconds']-362.77325166806986)<1e-10 and md==2455370
corrections=load(V/'parent-report-corrections01.json');assert corrections['full_Transfer']=='OPEN' and corrections['original_attempts_remaining']==0
plan=load(V/'publication-plan03.json');assert len(plan['entries'])==214 and sum(e['bytes'] for e in plan['entries'].values())==9013826
for p,e in plan['entries'].items():assert Path(p).stat().st_size==e['bytes'] and sha(p)==e['sha256']
out=dict(status='accepted_scoped_checkpoint',observed_UTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),final_manifest_sha256=sha(F/'final-result-manifest06.json'),publication_plan_sha256=sha(V/'publication-plan03.json'),publication_plan_pending_review_field_closed_by_this_disposition=True,actual_final_Opus_review=record(V/'opus55-final-call14-review03.json'),actual_mathematical_Opus_review=record(V/'opus55-final-call14-review02.json'),actual_review_returncode=0,actual_mathematical_review_returncode=0,review_scope='Actual review02 mathematical endpoint/controls/source; actual review03 full listed source/helpers/parent reports with explicitly partial portable/mapping/type census reads. SOURCE reviews are separate from parent original RAW kernel evidence inspection.',report_corrections=record(V/'parent-report-corrections01.json'),current_pre_staging_budget=budget,actual_flat_runtime_metadata_bytes=md,original_ALL_attempts=60,original_ALL_remaining=0,successful_modules=57,retained_actual_type_axiom_audits=398,failed_ordinals=[55,56,58],whole_module_credit_for_failures=0,independent_portable_check=dict(all60receipt_fields_equal_original=True,all182deduplicated_records_equal_original=True,original_observed_fields_unchanged=True),source_reproduction='57 accepted source bytes independently regenerated, no accepted kernel replay; original local identity prerequisites remain required.',historical_inputs_outside_Lean_sourcepaths=True,publication_conditions=['Publish only exact selected57 canonical modules, never historical Proof01/Checked01/Controls01 on sourcepath','Preserve original snapshots and append-only count/wording corrections','Publish neither RAWlogs/proofobjects/caches/toolchains/DB nor standalone originalobject replay claim','Keep maintained/generated changes separate, runtime lock exact and full Transfer OPEN'],mathematical_scope=dict(steps=628,selected_rows=837,domain=24,arity=6,original_columns=[23,24,30,31,32,33],write_window=[23472,24308],prior_rows='Only given initial satisfaction and actual support outside the window',controls='13 local syntax/representative row identity/fixed metadata checker-false conclusions; no semantic inequality or whole production checker'),OPEN=corrections['explicit_OPEN'],Join15='UNRUN/BLOCKED aggregate metadata and first-cache shadow; no initialization or admission',foreign='Original3ALL exhausted',native='OriginalTOTAL unknown; zero new execution',new_Lean_runs_for_parent_review=0,final_certification_refresh=False,full_Transfer='OPEN')
(V/'parent-acceptance01.json').open('x').write(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(disposition=record(V/'parent-acceptance01.json'),current_pre_staging_budget=budget,actual_flat_metadata_bytes=md,new_Lean_runs=0)))
