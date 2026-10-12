from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-input-semantics-endpoint-20261012-03/assemble.py').read_text()
for a,b in [
 ("CURRENT=DIAG/'transfer-scalar-input-semantics-20261012-04'","CURRENT=DIAG/'transfer-scalar-extended-semantics-20261012-01'"),
 ("CHECKPOINT=DIAG/'transfer-scalar-input-semantics-checkpoint-20261012-04'","CHECKPOINT=DIAG/'transfer-scalar-extended-semantics-checkpoint-20261012-01'"),
 ("MODULE='TransferScalarInputSemantics01'","MODULE='TransferScalarExtendedSemantics01'"),
 ("PARENT=DIAG/'transfer-scalar-additive-field-endpoint-20261012-02'","PARENT=DIAG/'transfer-scalar-input-semantics-endpoint-20261012-03'"),
 ("archive=ROOT/'portable-windows-scalar-input-semantics-endpoint01.tar.xz'","archive=ROOT/'portable-windows-scalar-extended-semantics-endpoint01.tar.xz'"),
 ("parent_archive=PARENT/'portable-windows-scalar-additive-field-endpoint01.tar.xz'","parent_archive=PARENT/'portable-windows-scalar-input-semantics-endpoint01.tar.xz'"),
 ('20d1bad2c5b67ddf1f03cf438dbc1716b1bc5b57275842c3d04380d9b35277b8','30b878090316f13c75af4643e298052137f4680843d231f4d5864fa69946a343'),
 ("kinds.count('def')==1 and kinds.count('theorem')==6","kinds.count('def')==2 and kinds.count('theorem')==5"),
 ("pool['objects']==212 and len(pool['inherited_public_reports'])==1513","pool['objects']==213 and len(pool['inherited_public_reports'])==1520"),
 ("t.extractfile('reports/fresh-8-complete-declarations.txt')","t.extractfile('reports/fresh-7-complete-declarations.txt')"),
 ('len(parent_reports)==8','len(parent_reports)==7'),
 ("'module':'TransferScalarAdditiveField01'","'module':'TransferScalarInputSemantics01'"),
 ("len(parent_selected)==212 and len(pool['selected'])==212","len(parent_selected)==213 and len(pool['selected'])==213"),
 ("'complete_owned_modules':212,'inherited_complete_reports':1513","'complete_owned_modules':213,'inherited_complete_reports':1520"),
 ('original212-module1513-report','original213-module1520-report'),
 ("['prepare.py','prepare_from01.py','prepare_from02.py','prepare_from03.py','prepare_recipe.py'","['prepare.py','prepare_recipe.py'"),
 ('handwritten complete independent field/refusal semantics and structural induction over the source input evaluator','handwritten complete independent constant/u64/random/square/power/inverse/selection semantics and structural source evaluator induction'),
 ('qualified212-module first import root and1513','qualified213-module first import root and1520'),
 ('scalar-input-semantics-shape.json','scalar-extended-semantics-shape.json'),
 ('SOURCE_SCALAR_INPUT_EVALUATOR_INDEPENDENT_FIELD_AND_REFUSAL_SEMANTICS_QUALIFIED','SOURCE_SCALAR_EXTENDED_EVALUATOR_INDEPENDENT_FIELD_AND_REFUSAL_SEMANTICS_QUALIFIED'),
 ("'fresh_definition_audits':1","'fresh_definition_audits':2"),
 ("'fresh_theorem_audits':6","'fresh_theorem_audits':5"),
 ("'inherited_complete_public_audits':1513","'inherited_complete_public_audits':1520"),
 ("'rejected_attempts':2","'rejected_attempts':0"),
 ('transfer-scalar-input-semantics-endpoint-v1','transfer-scalar-extended-semantics-endpoint-v1'),
 ("'fresh_audits':7,'inherited_audits':1513","'fresh_audits':7,'inherited_audits':1520")]:
 expected=3 if a=='scalar-input-semantics-shape.json' else 2 if a=="'fresh_audits':7,'inherited_audits':1513" else 1
 assert s.count(a)==expected,(a,s.count(a),expected);s=s.replace(a,b)
start=s.index("failed=DIAG/'transfer-scalar-input-semantics-20261012-01'");end=s.index('add(Path(__file__)',start);s=s[:start]+s[end:]
(ROOT/'assemble.py').write_bytes(s.encode())
print({'fresh7_declarations','independent_whole_extended_evaluator','complete213_module1520_report_input_semantics_predecessor','no_ancestor_replay'})
