from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
def pin(p):
 p=Path(p);b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
(ROOT/'context').mkdir()
scope='Six complete source-model declarations compose qualified exact word-mask power with its mathematical field exponent and exact equality-derived inversion refusal byte with the qualified source inversion. Returned inverses multiply to mathematical and raw source ONE. Canonical self is the explicit typed model domain. No desired field/flag/output premise is used. This observes returned Option values, not timing or eager computation effects. Rust compiler/volatile barrier/native CtOption implementation/ABI/all caller origins/full Transfer remain open.'
context={'scope':scope,'source_choice_masks':pin(DIAG/'transfer-scalar-choice-masks-20261012-05/context/scalar-choice-masks-shape.json'),'source_constant_equality':pin(DIAG/'transfer-scalar-constant-equality-20261012-04/context/scalar-constant-equality-shape.json'),'source_pow_field':pin(DIAG/'transfer-scalar-pow-field-20261012-08/context/scalar-pow-field-shape.json'),'source_inverse_correctness':pin(DIAG/'transfer-scalar-inverse-correctness-20261012-04/context/scalar-inverse-correctness-shape.json')}
(ROOT/'context/scalar-choice-correspondence-shape.json').write_text(json.dumps(context,indent=2,sort_keys=True)+'\n')
s=(DIAG/'transfer-scalar-public-orders-20261012-04/prepare.py').read_text()
s=s.replace("POOL = DIAG / 'transfer-scalar-public-orders-owned-floor-20261012-02'","POOL = DIAG / 'transfer-scalar-choice-correspondence-owned-floor-20261012-01'")
s=s.replace("MODULE = 'TransferScalarPublicOrders01'","MODULE = 'TransferScalarChoiceCorrespondence01'")
s=s.replace("assert not (ROOT / 'plan.json').exists() and POOL.exists()","assert not (ROOT / 'plan.json').exists() and not POOL.exists()")
extra="""for dirname,module,count in [
 ('transfer-scalar-pow-bit-integer-20261012-03','TransferScalarPowBitInteger01',6),
 ('transfer-scalar-pow-field-20261012-08','TransferScalarPowField01',6),
 ('transfer-scalar-choice-masks-20261012-05','TransferScalarChoiceMasks01',21),
 ('transfer-scalar-constant-equality-20261012-04','TransferScalarConstantEquality01',12)]:
 leaf=DIAG/dirname;leafPlan=json.loads((leaf/'plan.json').read_bytes())
 leafEvents=[json.loads(line) for line in (leaf/'events.jsonl').read_text().splitlines()]
 assert len(leafEvents)==2 and leafEvents[-1]['result']['status']=='passed'
 leafPool=json.loads(Path(leafPlan['owned_import_pool']['path']).read_bytes())
 known={name:(source,obj) for name,source,obj in records}
 for row in leafPool['selected']:
  assert known[row['module']]==(row['source'],row['object'])
 for name,report in leafPool['inherited_public_reports'].items():assert audits[name]==report
 leafStdout=leaf/'runs'/('01-'+module)/'stdout.txt'
 fresh=m.audit(leafStdout.read_text(),leafPlan['targets'][0]['audit_names'])
 assert len(fresh)==count and fresh==leafEvents[-1]['result']['audits']
 assert pin(leafStdout)==leafEvents[-1]['result']['stdout'] and set(audits).isdisjoint(fresh)
 audits.update(fresh)
 records.append((module,leafPlan['targets'][0]['source'],leafEvents[-1]['result']['objects'][0]))
 inputs += leafPool['input_records']
 inputs += [pin(leaf/n) for n in ['plan.json','events.jsonl','execute_bounded.py','source-mapping.json','review.json','handwritten/'+module+'.lean','project/ShielddSecurity/'+module+'.lean']]
 inputs.append(pin(leafStdout));inputs.append(pin(Path(leafPlan['owned_import_pool']['path'])))
assert len(records)==207 and len(audits)==1467
"""
at=s.index('originalInputs=inputs[:]');s=s[:at]+extra+s[at:]
start=s.index("composition_file=POOL/'composition-review.json'");end=s.index('handwritten = ROOT',start)
composition="""POOL.mkdir();selected=[]
for module,source,obj in records:
 assert pin(source['path'])==source and pin(obj['path'])==obj
 copy=POOL/'modules/ShielddSecurity'/(module+'.olean');copy.parent.mkdir(parents=True,exist_ok=True)
 shutil.copyfile(obj['path'],copy);assert pin(copy)['sha256']==obj['sha256']
 selected.append({'module':module,'source':source,'object':obj,'copy':pin(copy)});inputs += [source,obj]
composition={'admission_ready':True,'kernel_credit':0,'objects':207,'selected':selected,'input_records':inputs,'inherited_public_reports':audits,'charged_new_object_bytes':sum(row['copy']['bytes'] for row in selected),'field_foundation':old_pool['field_foundation'],'scope':'Complete207-module1467-report first import root: exact inverse/prime, bit reconstruction, power field, word masks and equality branches merged without ancestor replay. Shared source/object/report identities equal; no semantic or native result inferred from hashes.'}
composition_file=POOL/'composition-review.json';dump(composition_file,composition)
"""
s=s[:start]+composition+s[end:]
s=s.replace('assert len(names) == 7','assert len(names) == 6').replace("'fresh_audits': 7","'fresh_audits': 6")
s=s.replace('scalar_public_orders_source_shape','scalar_choice_correspondence_source_shape').replace('scalar-public-orders-shape.json','scalar-choice-correspondence-shape.json')
old="'imports': ['ShielddSecurity.TransferScalarInverseCorrectness01', 'Mathlib.GroupTheory.OrderOfElement']"
assert s.count(old)==1
s=s.replace(old,"'imports': ['ShielddSecurity.TransferScalarChoiceMasks01', 'ShielddSecurity.TransferScalarConstantEquality01', 'ShielddSecurity.TransferScalarPowField01', 'ShielddSecurity.TransferScalarInverseCorrectness01']")
start=s.index("mapping['interfaces'] =");end=s.index('\n',start)
s=s[:start]+"mapping['interfaces'] = prior_mapping['interfaces'] + [json.loads((ROOT/'context/scalar-choice-correspondence-shape.json').read_text())['scope']]"+s[end:]
start=s.index('unpreparedOrders=DIAG/');end=s.index("plan['artifact_policy']",start);s=s[:start]+s[end:]
extra="""choiceCorrespondenceContext=json.loads((ROOT/'context/scalar-choice-correspondence-shape.json').read_text())
plan['pins'] += [choiceCorrespondenceContext[key] for key in ['source_choice_masks','source_constant_equality','source_pow_field','source_inverse_correctness']]
"""
at=s.index("plan['artifact_policy']");s=s[:at]+extra+s[at:]
s=s.replace('SCALAR_PUBLIC_ORDERS_COMPLETE_TWO_HUNDRED_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','SCALAR_CHOICE_CORRESPONDENCE_COMPLETE207_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
(ROOT/'prepare.py').write_text(s)
print({'all207_qualified_dependency_modules_merged':True,'inherited_complete_reports':1467,'fresh_declarations':6,'all_guards_unchanged':True,'ancestor_replay':False})
