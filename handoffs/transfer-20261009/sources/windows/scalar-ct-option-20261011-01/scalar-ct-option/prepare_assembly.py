from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-nullifier-field-domain-endpoint-20261012-02/assemble.py').read_text()
for a,b in [
 ("CURRENT=DIAG/'transfer-nullifier-field-domain-20261012-02'","CURRENT=DIAG/'transfer-scalar-ct-option-20261012-01'"),
 ("CHECKPOINT=DIAG/'transfer-nullifier-field-domain-checkpoint-20261012-02'","CHECKPOINT=DIAG/'transfer-scalar-ct-option-checkpoint-20261012-01'"),
 ("MODULE='TransferNullifierFieldDomain01'","MODULE='TransferScalarCtOption01'"),
 ("PARENT=DIAG/'transfer-nullifier-field-codec-endpoint-20261012-02'","PARENT=DIAG/'transfer-nullifier-field-domain-endpoint-20261012-02'"),
 ("archive=ROOT/'portable-windows-nullifier-field-domain-endpoint01.tar.xz'","archive=ROOT/'portable-windows-scalar-ct-option-endpoint01.tar.xz'"),
 ("parent_archive=PARENT/'portable-windows-nullifier-field-codec-endpoint01.tar.xz'","parent_archive=PARENT/'portable-windows-nullifier-field-domain-endpoint01.tar.xz'"),
 ('afdaf315803e886b508a9c3e5f7e5e8481ccc4c7ed3e726d599cb05e47b1327a','0a1a5a6080de0fccc1654057002bd57a87a4e922c7c27394aff397f3e7070d09'),
 ("kinds.count('theorem')==8","kinds.count('theorem')==7 and kinds.count('structure')==1"),
 ("pool['objects']==209 and len(pool['inherited_public_reports'])==1483","pool['objects']==210 and len(pool['inherited_public_reports'])==1494"),
 ("t.extractfile('reports/fresh-10-complete-declarations.txt')","t.extractfile('reports/fresh-11-complete-declarations.txt')"),
 ('len(parent_reports)==10','len(parent_reports)==11'),
 ("'module':'TransferNullifierFieldCodec01'","'module':'TransferNullifierFieldDomain01'"),
 ("len(parent_selected)==209 and len(pool['selected'])==209","len(parent_selected)==210 and len(pool['selected'])==210"),
 ("'complete_owned_modules':209,'inherited_complete_reports':1483","'complete_owned_modules':210,'inherited_complete_reports':1494"),
 ('original209-module1483-report','original210-module1494-report'),
 ("['prepare.py','prepare_from01.py','prepare_recipe.py'","['prepare.py','prepare_recipe.py'"),
 ('handwritten complete modeled field-residue domain and mutual-inverse theorem source','handwritten complete source CtOption constructor/field projections/Option conversion and decoder payload proof'),
 ('qualified209-module first import root and1483','qualified210-module first import root and1494'),
 ('nullifier-field-domain-shape.json','scalar-ct-option-shape.json'),
 ('SOURCE_NULLIFIER_ENTIRE_FIELD_RESIDUE_DOMAIN_MUTUAL_INVERSES_QUALIFIED','SOURCE_SCALAR_CT_OPTION_STORED_PAYLOAD_AND_CONVERSION_QUALIFIED'),
 ("'fresh_structure_audits':0,'fresh_theorem_audits':8","'fresh_structure_audits':1,'fresh_theorem_audits':7"),
 ("'inherited_complete_public_audits':1483","'inherited_complete_public_audits':1494"),
 ("'rejected_attempts':1","'rejected_attempts':0"),
 ('transfer-nullifier-field-domain-endpoint-v1','transfer-scalar-ct-option-endpoint-v1'),
 ("'fresh_audits':11,'inherited_audits':1483","'fresh_audits':11,'inherited_audits':1494")]:
 expected=3 if a=='nullifier-field-domain-shape.json' else 2 if a=="'fresh_audits':11,'inherited_audits':1483" else 1
 assert s.count(a)==expected,(a,s.count(a),expected);s=s.replace(a,b)
start=s.index("failed=DIAG/'transfer-nullifier-field-domain-20261012-01'");end=s.index('add(Path(__file__)',start);s=s[:start]+s[end:]
extra="""for key in ['subtle_locked_archive','subtle_source_copy','subtle_source_original','locked_cargo_manifest']:
 row=context['subtle_source_context'][key];assert pin(row['path'])==row and row in plan['pins']
 add(row['path'],'library/subtle-authenticated/'+key+'/'+Path(row['path']).name,'exact locked subtle crate checksum/source identity; static association, compiler/native ABI separate')
row=context['subtle_source_shape'];assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/original-choice-masks-shape.json','original independently qualified subtle source/crate/authentication association')
"""
at=s.index('add(Path(__file__)');s=s[:at]+extra+s[at:]
(ROOT/'assemble.py').write_bytes(s.encode())
print({'all11_declarations','locked_subtle_originals_retained','complete210_module1494_report_predecessor','no_ancestor_replay'})
