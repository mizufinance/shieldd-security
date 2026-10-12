from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-additive-field-endpoint-20261012-02/assemble.py').read_text()
for a,b in [
 ("CURRENT=DIAG/'transfer-scalar-additive-field-20261012-02'","CURRENT=DIAG/'transfer-scalar-input-semantics-20261012-01'"),
 ("CHECKPOINT=DIAG/'transfer-scalar-additive-field-checkpoint-20261012-02'","CHECKPOINT=DIAG/'transfer-scalar-input-semantics-checkpoint-20261012-01'"),
 ("MODULE='TransferScalarAdditiveField01'","MODULE='TransferScalarInputSemantics01'"),
 ("PARENT=DIAG/'transfer-scalar-ct-option-endpoint-20261012-01'","PARENT=DIAG/'transfer-scalar-additive-field-endpoint-20261012-02'"),
 ("archive=ROOT/'portable-windows-scalar-additive-field-endpoint01.tar.xz'","archive=ROOT/'portable-windows-scalar-input-semantics-endpoint01.tar.xz'"),
 ("parent_archive=PARENT/'portable-windows-scalar-ct-option-endpoint01.tar.xz'","parent_archive=PARENT/'portable-windows-scalar-additive-field-endpoint01.tar.xz'"),
 ('147795431e718b6dcb608d0fa4051ad7e9110027da99b1f4fd98cb74197b4dbe','20d1bad2c5b67ddf1f03cf438dbc1716b1bc5b57275842c3d04380d9b35277b8'),
 ('len(fresh)==8','len(fresh)==7'),
 ("len(kinds)==8 and kinds.count('def')==3 and kinds.count('theorem')==5","len(kinds)==7 and kinds.count('def')==1 and kinds.count('theorem')==6"),
 ("pool['objects']==211 and len(pool['inherited_public_reports'])==1505","pool['objects']==212 and len(pool['inherited_public_reports'])==1513"),
 ("t.extractfile('reports/fresh-11-complete-declarations.txt')","t.extractfile('reports/fresh-8-complete-declarations.txt')"),
 ('len(parent_reports)==11','len(parent_reports)==8'),
 ("'module':'TransferScalarCtOption01'","'module':'TransferScalarAdditiveField01'"),
 ("len(parent_selected)==211 and len(pool['selected'])==211","len(parent_selected)==212 and len(pool['selected'])==212"),
 ("'complete_owned_modules':211,'inherited_complete_reports':1505","'complete_owned_modules':212,'inherited_complete_reports':1513"),
 ('original211-module1505-report','original212-module1513-report'),
 ("['prepare.py','prepare_from01.py','prepare_recipe.py'","['prepare.py','prepare_recipe.py'"),
 ('handwritten complete derived mathematical source ADC/SBB/negation field arithmetic proof','handwritten complete independent field/refusal semantics and structural induction over the source input evaluator'),
 ("add(stdout,'reports/fresh-8-complete-declarations.txt'","add(stdout,'reports/fresh-7-complete-declarations.txt'"),
 ('qualified211-module first import root and1505','qualified212-module first import root and1513'),
 ('scalar-additive-field-shape.json','scalar-input-semantics-shape.json'),
 ('SOURCE_SCALAR_ADDITIVE_MATHEMATICAL_FIELD_OPERATIONS_QUALIFIED','SOURCE_SCALAR_INPUT_EVALUATOR_INDEPENDENT_FIELD_AND_REFUSAL_SEMANTICS_QUALIFIED'),
 ("'fresh_definition_audits':3","'fresh_definition_audits':1"),
 ("'fresh_theorem_audits':5","'fresh_theorem_audits':6"),
 ("'fresh_complete_public_audits':8","'fresh_complete_public_audits':7"),
 ("'inherited_complete_public_audits':1505","'inherited_complete_public_audits':1513"),
 ("'rejected_attempts':1","'rejected_attempts':0"),
 ('transfer-scalar-additive-field-endpoint-v1','transfer-scalar-input-semantics-endpoint-v1'),
 ("'fresh_audits':8,'inherited_audits':1505","'fresh_audits':7,'inherited_audits':1513")]:
 expected=3 if a=='scalar-additive-field-shape.json' else 2 if a=="'fresh_audits':8,'inherited_audits':1505" else 1
 assert s.count(a)==expected,(a,s.count(a),expected);s=s.replace(a,b)
start=s.index("failed=DIAG/'transfer-scalar-additive-field-20261012-01'");end=s.index('add(Path(__file__)',start);s=s[:start]+s[end:]
(ROOT/'assemble.py').write_bytes(s.encode())
print({'fresh7_declarations','independent_model_not_expected_output_premise','complete212_module1513_report_predecessor','no_ancestor_replay'})
