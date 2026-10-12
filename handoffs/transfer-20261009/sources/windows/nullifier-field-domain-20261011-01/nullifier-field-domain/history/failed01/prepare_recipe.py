from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-nullifier-field-codec-20261012-01/prepare.py').read_text()
for a,b in [
 ("UP=DIAG/'transfer-scalar-choice-correspondence-20261012-01'","UP=DIAG/'transfer-nullifier-field-codec-20261012-03'"),
 ("POOL=DIAG/'transfer-nullifier-field-codec-owned-floor-20261012-01'","POOL=DIAG/'transfer-nullifier-field-domain-owned-floor-20261012-01'"),
 ("MODULE='TransferNullifierFieldCodec01'","MODULE='TransferNullifierFieldDomain01'"),
 ('runs/01-TransferScalarChoiceCorrespondence01/stdout.txt','runs/01-TransferNullifierFieldCodec01/stdout.txt'),
 ('len(current)==6','len(current)==10'),
 ("records.append(('TransferScalarChoiceCorrespondence01'","records.append(('TransferNullifierFieldCodec01'"),
 ('len(records)==208 and len(audits)==1473','len(records)==209 and len(audits)==1483'),
 ("['prepare_recipe.py','prepare.py'","['prepare_from02.py','prepare.py'"),
 ('handwritten/TransferScalarChoiceCorrespondence01.lean','handwritten/TransferNullifierFieldCodec01.lean'),
 ('project/ShielddSecurity/TransferScalarChoiceCorrespondence01.lean','project/ShielddSecurity/TransferNullifierFieldCodec01.lean'),
 ("'objects':208","'objects':209"),
 ('qualified208-module1473-report','qualified209-module1483-report'),
 ('len(names)==10','len(names)==11'),
 ('nullifier-field-codec-shape.json','nullifier-field-domain-shape.json'),
 ('nullifier_field_codec_source_shape','nullifier_field_domain_source_shape'),
 ("'imports':['ShielddSecurity.TransferScalarInputFamily01','ShielddSecurity.TransferScalarChoiceMasks01']","'imports':['ShielddSecurity.TransferNullifierFieldCodec01']"),
 ('exact208-module qualified','exact209-module qualified'),
 ("'fresh_audits':10","'fresh_audits':11"),
 ('NULLIFIER_FIELD_CODEC_SELF_REVIEWED_UNRUN','NULLIFIER_FIELD_DOMAIN_SELF_REVIEWED_UNRUN')]:
 assert s.count(a)==1,(a,s.count(a));s=s.replace(a,b)
start=s.index("scope='");end=s.index('\n',start)
scope='Eleven complete source-model declarations derive full legal field-residue coverage. Every Fin(p) value has exact32 finite little-endian bytes accepted by the source-shaped Nullifier decoder, whose actual R2 payload derives that mathematical field value and the original bytes. Constructor and source serializer residue projection are mutual inverses on every canonical raw source field. No desired output assumption. Exact Fq alias association remains separate; native private constructor origins/compiler/slice/CtOption/ABI/callers/full Transfer remain open. No subgroup-scalar or timing claim.'
s=s[:start]+"scope="+repr(scope)+s[end:]
at=s.index("plan['artifact_policy']")
s=s[:at]+"plan['pins'] += [pin(ROOT/'prepare_recipe.py')]\n"+s[at:]
(ROOT/'prepare.py').write_bytes(s.encode())
print({'full209_module1483_report_predecessor_reused':True,'fresh11_declarations':True,'original_guards_unchanged':True,'no_ancestor_replay':True})
