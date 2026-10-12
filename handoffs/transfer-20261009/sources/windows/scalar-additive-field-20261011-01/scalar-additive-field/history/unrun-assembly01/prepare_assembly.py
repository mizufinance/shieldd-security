from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-ct-option-endpoint-20261012-01/assemble.py').read_text()
for a,b in [
 ("CURRENT=DIAG/'transfer-scalar-ct-option-20261012-01'","CURRENT=DIAG/'transfer-scalar-additive-field-20261012-01'"),
 ("CHECKPOINT=DIAG/'transfer-scalar-ct-option-checkpoint-20261012-01'","CHECKPOINT=DIAG/'transfer-scalar-additive-field-checkpoint-20261012-01'"),
 ("MODULE='TransferScalarCtOption01'","MODULE='TransferScalarAdditiveField01'"),
 ("PARENT=DIAG/'transfer-nullifier-field-domain-endpoint-20261012-02'","PARENT=DIAG/'transfer-scalar-ct-option-endpoint-20261012-01'"),
 ("archive=ROOT/'portable-windows-scalar-ct-option-endpoint01.tar.xz'","archive=ROOT/'portable-windows-scalar-additive-field-endpoint01.tar.xz'"),
 ("parent_archive=PARENT/'portable-windows-nullifier-field-domain-endpoint01.tar.xz'","parent_archive=PARENT/'portable-windows-scalar-ct-option-endpoint01.tar.xz'"),
 ('0a1a5a6080de0fccc1654057002bd57a87a4e922c7c27394aff397f3e7070d09','147795431e718b6dcb608d0fa4051ad7e9110027da99b1f4fd98cb74197b4dbe'),
 ('len(fresh)==11','len(fresh)==8'),
 ("len(kinds)==11 and kinds.count('def')==3 and kinds.count('theorem')==7 and kinds.count('structure')==1","len(kinds)==8 and kinds.count('def')==3 and kinds.count('theorem')==5 and kinds.count('structure')==0"),
 ("pool['objects']==210 and len(pool['inherited_public_reports'])==1494","pool['objects']==211 and len(pool['inherited_public_reports'])==1505"),
 ("'module':'TransferNullifierFieldDomain01'","'module':'TransferScalarCtOption01'"),
 ("len(parent_selected)==210 and len(pool['selected'])==210","len(parent_selected)==211 and len(pool['selected'])==211"),
 ("'complete_owned_modules':210,'inherited_complete_reports':1494","'complete_owned_modules':211,'inherited_complete_reports':1505"),
 ('original210-module1494-report','original211-module1505-report'),
 ('handwritten complete source CtOption constructor/field projections/Option conversion and decoder payload proof','handwritten complete derived mathematical source ADC/SBB/negation field arithmetic proof'),
 ("add(stdout,'reports/fresh-11-complete-declarations.txt'","add(stdout,'reports/fresh-8-complete-declarations.txt'"),
 ('qualified210-module first import root and1494','qualified211-module first import root and1505'),
 ('scalar-ct-option-shape.json','scalar-additive-field-shape.json'),
 ('SOURCE_SCALAR_CT_OPTION_STORED_PAYLOAD_AND_CONVERSION_QUALIFIED','SOURCE_SCALAR_ADDITIVE_MATHEMATICAL_FIELD_OPERATIONS_QUALIFIED'),
 ("'fresh_structure_audits':1,'fresh_theorem_audits':7","'fresh_structure_audits':0,'fresh_theorem_audits':5"),
 ("'fresh_complete_public_audits':11","'fresh_complete_public_audits':8"),
 ("'inherited_complete_public_audits':1494","'inherited_complete_public_audits':1505"),
 ('transfer-scalar-ct-option-endpoint-v1','transfer-scalar-additive-field-endpoint-v1'),
 ("'fresh_audits':11,'inherited_audits':1494","'fresh_audits':8,'inherited_audits':1505")]:
 expected=3 if a=='scalar-ct-option-shape.json' else 2 if a=="'fresh_audits':11,'inherited_audits':1494" else 1
 assert s.count(a)==expected,(a,s.count(a),expected);s=s.replace(a,b)
(ROOT/'assemble.py').write_bytes(s.encode())
print({'fresh8_declarations','source_word_contracts_retained','complete211_module1505_report_predecessor','no_ancestor_replay'})
