from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-scalar-ct-option-20261012-01/prepare.py').read_text()
for a,b in [
 ("UP=DIAG/'transfer-nullifier-field-domain-20261012-02'","UP=DIAG/'transfer-scalar-ct-option-20261012-01'"),
 ("POOL=DIAG/'transfer-scalar-ct-option-owned-floor-20261012-01'","POOL=DIAG/'transfer-scalar-additive-field-owned-floor-20261012-01'"),
 ("MODULE='TransferScalarCtOption01'","MODULE='TransferScalarAdditiveField01'"),
 ('runs/01-TransferNullifierFieldDomain01/stdout.txt','runs/01-TransferScalarCtOption01/stdout.txt'),
 ("records.append(('TransferNullifierFieldDomain01'","records.append(('TransferScalarCtOption01'"),
 ('len(records)==210 and len(audits)==1494','len(records)==211 and len(audits)==1505'),
 ("'prepare_from01.py'","'prepare_recipe.py'"),
 ('handwritten/TransferNullifierFieldDomain01.lean','handwritten/TransferScalarCtOption01.lean'),
 ('project/ShielddSecurity/TransferNullifierFieldDomain01.lean','project/ShielddSecurity/TransferScalarCtOption01.lean'),
 ("'objects':210","'objects':211"),
 ('qualified210-module1494-report','qualified211-module1505-report'),
 ('len(names)==11','len(names)==8'),
 ('scalar-ct-option-shape.json','scalar-additive-field-shape.json'),
 ('scalar_ct_option_source_shape','scalar_additive_field_source_shape'),
 ("'imports':['ShielddSecurity.TransferNullifierFieldDomain01']","'imports':['ShielddSecurity.TransferScalarCtOption01']"),
 ('exact210-module qualified','exact211-module qualified'),
 ("'fresh_audits':11","'fresh_audits':8"),
 ('SCALAR_CT_OPTION_SELF_REVIEWED_UNRUN','SCALAR_ADDITIVE_FIELD_SELF_REVIEWED_UNRUN')]:
 expected=2 if a=='scalar_ct_option_source_shape' else 1
 assert s.count(a)==expected,(a,s.count(a),expected);s=s.replace(a,b)
start=s.index("scope='");end=s.index('\n',start)
scope='Eight complete source-model declarations derive exact mathematical field addition/subtraction/negation from qualified ADC/SBB/masked-addback/nonzero-mask word outputs. Three canonical operation wrappers obtain output widths/ranges from original source contracts. Two small symbolic lemmas derive subtraction by uniquely solving the canonical additive residue equation and removing Montgomery scaling. No desired mathematical output premise in operation theorems. Typed canonical inputs explicit. Compiler/native private origins/ABI/all native callers/full Transfer remain open.'
s=s[:start]+"scope="+repr(scope)+s[end:]
(ROOT/'prepare.py').write_bytes(s.encode())
print({'full211_module1505_report_predecessor','fresh8_declarations','all_guards_unchanged','no_ancestor_replay'})
