from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-scalar-additive-field-20261012-01/prepare.py').read_text()
for a,b in [
 ("UP=DIAG/'transfer-scalar-ct-option-20261012-01'","UP=DIAG/'transfer-scalar-additive-field-20261012-02'"),
 ("POOL=DIAG/'transfer-scalar-additive-field-owned-floor-20261012-01'","POOL=DIAG/'transfer-scalar-input-semantics-owned-floor-20261012-01'"),
 ("MODULE='TransferScalarAdditiveField01'","MODULE='TransferScalarInputSemantics01'"),
 ('runs/01-TransferScalarCtOption01/stdout.txt','runs/01-TransferScalarAdditiveField01/stdout.txt'),
 ('len(current)==11','len(current)==8'),
 ("records.append(('TransferScalarCtOption01'","records.append(('TransferScalarAdditiveField01'"),
 ('len(records)==211 and len(audits)==1505','len(records)==212 and len(audits)==1513'),
 ('handwritten/TransferScalarCtOption01.lean','handwritten/TransferScalarAdditiveField01.lean'),
 ('project/ShielddSecurity/TransferScalarCtOption01.lean','project/ShielddSecurity/TransferScalarAdditiveField01.lean'),
 ("'objects':211","'objects':212"),
 ('qualified211-module1505-report','qualified212-module1513-report'),
 ('len(names)==8','len(names)==7'),
 ('scalar-additive-field-shape.json','scalar-input-semantics-shape.json'),
 ('scalar_additive_field_source_shape','scalar_input_semantics_source_shape'),
 ("'imports':['ShielddSecurity.TransferScalarCtOption01']","'imports':['ShielddSecurity.TransferScalarAdditiveField01']"),
 ('exact211-module qualified','exact212-module qualified'),
 ("'fresh_audits':8","'fresh_audits':7"),
 ('SCALAR_ADDITIVE_FIELD_SELF_REVIEWED_UNRUN','SCALAR_INPUT_SEMANTICS_SELF_REVIEWED_UNRUN')]:
 expected=2 if a=='scalar_additive_field_source_shape' else 1
 assert s.count(a)==expected,(a,s.count(a),expected);s=s.replace(a,b)
start=s.index("scope='");end=s.index('\n',start)
scope='Seven complete source-model declarations give independent integer-residue and refusal semantics for the entire represented ScalarInputProgram evaluator. Raw4-word and wide64-byte constructors reduce the actual decoded integer; canonical32-byte construction accepts iff below modulus and returns that exact integer. Binary/unary Option lifting and structural program induction compose add/sub/mul/neg/double proofs and constructor failures. No desired output or success flag premise in the complete evaluator theorem. Represented source operation family explicit; compiler/ABI/private origins/native caller census/full Transfer remain open.'
s=s[:start]+"scope="+repr(scope)+s[end:]
(ROOT/'prepare.py').write_bytes(s.encode())
print({'fresh7_declarations','full212_module1513_report_predecessor','all_guards_unchanged','no_ancestor_replay'})
