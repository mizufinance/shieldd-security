from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-nullifier-field-codec-endpoint-20261012-02/assemble.py').read_text()
for a,b in [
 ("CURRENT=DIAG/'transfer-nullifier-field-codec-20261012-03'","CURRENT=DIAG/'transfer-nullifier-field-domain-20261012-01'"),
 ("CHECKPOINT=DIAG/'transfer-nullifier-field-codec-checkpoint-20261012-03'","CHECKPOINT=DIAG/'transfer-nullifier-field-domain-checkpoint-20261012-01'"),
 ("MODULE='TransferNullifierFieldCodec01'","MODULE='TransferNullifierFieldDomain01'"),
 ("PARENT=DIAG/'transfer-scalar-choice-correspondence-endpoint-20261012-02'","PARENT=DIAG/'transfer-nullifier-field-codec-endpoint-20261012-02'"),
 ("archive=ROOT/'portable-windows-nullifier-field-codec-endpoint01.tar.xz'","archive=ROOT/'portable-windows-nullifier-field-domain-endpoint01.tar.xz'"),
 ("parent_archive=PARENT/'portable-windows-scalar-choice-correspondence-endpoint01.tar.xz'","parent_archive=PARENT/'portable-windows-nullifier-field-codec-endpoint01.tar.xz'"),
 ('342a74d38b2133d0cad45b1e79ede9fa6957731bf8cfa5f208e2277747dfbad1','afdaf315803e886b508a9c3e5f7e5e8481ccc4c7ed3e726d599cb05e47b1327a'),
 ('len(fresh)==10','len(fresh)==11'),
 ("len(kinds)==10 and kinds.count('def')==2","len(kinds)==11 and kinds.count('def')==3"),
 ("pool['objects']==208 and len(pool['inherited_public_reports'])==1473","pool['objects']==209 and len(pool['inherited_public_reports'])==1483"),
 ('reports/fresh-6-complete-declarations.txt','reports/fresh-10-complete-declarations.txt'),
 ('len(parent_reports)==6','len(parent_reports)==10'),
 ("'module':'TransferScalarChoiceCorrespondence01'","'module':'TransferNullifierFieldCodec01'"),
 ("len(parent_selected)==208 and len(pool['selected'])==208","len(parent_selected)==209 and len(pool['selected'])==209"),
 ("'complete_owned_modules':208,'inherited_complete_reports':1473","'complete_owned_modules':209,'inherited_complete_reports':1483"),
 ('original208-module1473-report','original209-module1483-report'),
 ("'prepare_from02.py'","'prepare_recipe.py'"),
 ('handwritten complete source-shaped Nullifier codec theorem source','handwritten complete modeled field-residue domain and mutual-inverse theorem source'),
 ("add(stdout,'reports/fresh-10-complete-declarations.txt'","add(stdout,'reports/fresh-11-complete-declarations.txt'"),
 ('qualified208-module first import root and1473','qualified209-module first import root and1483'),
 ('nullifier-field-codec-shape.json','nullifier-field-domain-shape.json'),
 ('SOURCE_NULLIFIER_FIELD_CODEC_FULL_BYTE_LIST_DOMAIN_QUALIFIED','SOURCE_NULLIFIER_ENTIRE_FIELD_RESIDUE_DOMAIN_MUTUAL_INVERSES_QUALIFIED'),
 ("'fresh_definition_audits':2","'fresh_definition_audits':3"),
 ("'fresh_complete_public_audits':10","'fresh_complete_public_audits':11"),
 ("'inherited_complete_public_audits':1473","'inherited_complete_public_audits':1483"),
 ("'rejected_attempts':2","'rejected_attempts':0"),
 ('transfer-nullifier-field-codec-endpoint-v1','transfer-nullifier-field-domain-endpoint-v1'),
 ("'fresh_audits':10,'inherited_audits':1473","'fresh_audits':11,'inherited_audits':1483")]:
 assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b)
start=s.index("for attempt in ['01','02']:");end=s.index('add(Path(__file__)',start)
s=s[:start]+"add(ROOT/'prepare_assembly.py','prepare_assembly.py','exact fresh assembly derivation')\n"+s[end:]
(ROOT/'assemble.py').write_bytes(s.encode())
print({'fresh11_declarations','exact_parent_codec_archive','all209_original_source_identities','no_ancestor_replay'})
