from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-scalar-input-semantics-20261012-01/prepare.py').read_text()
for a,b in [
 ("UP=DIAG/'transfer-scalar-additive-field-20261012-02'","UP=DIAG/'transfer-scalar-input-semantics-20261012-04'"),
 ("POOL=DIAG/'transfer-scalar-input-semantics-owned-floor-20261012-01'","POOL=DIAG/'transfer-scalar-extended-semantics-owned-floor-20261012-01'"),
 ("MODULE='TransferScalarInputSemantics01'","MODULE='TransferScalarExtendedSemantics01'"),
 ('runs/01-TransferScalarAdditiveField01/stdout.txt','runs/01-TransferScalarInputSemantics01/stdout.txt'),
 ('len(current)==8','len(current)==7'),
 ("records.append(('TransferScalarAdditiveField01'","records.append(('TransferScalarInputSemantics01'"),
 ('len(records)==212 and len(audits)==1513','len(records)==213 and len(audits)==1520'),
 ('handwritten/TransferScalarAdditiveField01.lean','handwritten/TransferScalarInputSemantics01.lean'),
 ('project/ShielddSecurity/TransferScalarAdditiveField01.lean','project/ShielddSecurity/TransferScalarInputSemantics01.lean'),
 ("'objects':212","'objects':213"),
 ('qualified212-module1513-report','qualified213-module1520-report'),
 ('scalar-input-semantics-shape.json','scalar-extended-semantics-shape.json'),
 ('scalar_input_semantics_source_shape','scalar_extended_semantics_source_shape'),
 ("'imports':['ShielddSecurity.TransferScalarAdditiveField01']","'imports':['ShielddSecurity.TransferScalarInputSemantics01','ShielddSecurity.TransferScalarPowField01','ShielddSecurity.TransferScalarInvertField01']"),
 ('exact212-module qualified','exact213-module qualified'),
 ('SCALAR_INPUT_SEMANTICS_SELF_REVIEWED_UNRUN','SCALAR_EXTENDED_SEMANTICS_SELF_REVIEWED_UNRUN')]:
 expected=2 if a=='scalar_input_semantics_source_shape' else 1
 assert s.count(a)==expected,(a,s.count(a),expected);s=s.replace(a,b)
start=s.index("scope='");end=s.index('\n',start)
scope='Seven complete source-model declarations state independent integer/refusal semantics for the complete represented ScalarExtendedProgram evaluator. Separate kernel-checked public integer constants, exact u64, random64-byte residue, input-program semantics, add/sub/mul/neg/double/square/pow/pow_vartime, inversion zero refusal and exponent, and eager Boolean selection are composed by structural induction. No desired output or success flag assumption in the whole evaluator theorem. The source inversion payload is derived from its well-formed chain. Returned values/failure projection only; RNG distribution/eager side effects/native private origins/compiler/ABI/native caller census/full Transfer remain open.'
s=s[:start]+"scope="+repr(scope)+s[end:]
(ROOT/'prepare.py').write_bytes(s.encode())
print({'fresh7_declarations','exact213_module1520_report_input_semantics_predecessor','root_public_orders_branch_independently_retained','all_guards_unchanged','no_ancestor_replay'})
