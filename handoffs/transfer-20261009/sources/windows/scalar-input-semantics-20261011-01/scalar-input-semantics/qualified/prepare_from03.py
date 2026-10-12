from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent;old=DIAG/'transfer-scalar-input-semantics-20261012-03'
assert not (ROOT/'prepare.py').exists()
source=(old/'handwritten/TransferScalarInputSemantics01.lean').read_text()
assert source.count('import ShielddSecurity.TransferScalarAdditiveField01')==1
source=source.replace('import ShielddSecurity.TransferScalarAdditiveField01','import ShielddSecurity.TransferScalarAdditiveField01\nimport ShielddSecurity.TransferScalarFieldValues01')
for theorem,op in [
 ('TransferScalarAdditiveField01.actual_source_canonical_add_has_exact_mathematical_field_sum','sourceCanonicalAdd (fun x y => (x + y) % nullifierModulus)'),
 ('TransferScalarAdditiveField01.actual_source_canonical_sub_has_exact_mathematical_field_difference','sourceCanonicalSub (fun x y => (x + nullifierModulus - y) % nullifierModulus)'),
 ('TransferScalarFieldValues01.actual_modeled_canonical_multiply_has_exact_mathematical_field_value','sourceCanonicalMul (fun x y => (x * y) % nullifierModulus)')]:
 before='mapped_canonical_option_binary_operation_preserves_derived_field_semantics _ _ _ _\n      '+theorem
 assert source.count(before)==1
 source=source.replace(before,'mapped_canonical_option_binary_operation_preserves_derived_field_semantics _ _ '+op+'\n      '+theorem)
before='mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ _ _\n      TransferScalarAdditiveField01.actual_source_canonical_negation_has_exact_mathematical_field_value'
assert source.count(before)==1
source=source.replace(before,'mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ sourceCanonicalNeg (fun x => (nullifierModulus - x) % nullifierModulus)\n      TransferScalarAdditiveField01.actual_source_canonical_negation_has_exact_mathematical_field_value')
before='mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ _ _\n      (fun a => TransferScalarAdditiveField01.actual_source_canonical_add_has_exact_mathematical_field_sum a a)'
assert source.count(before)==1
source=source.replace(before,'mapped_canonical_option_unary_operation_preserves_derived_field_semantics _ (fun a => sourceCanonicalAdd a a) (fun x => (x + x) % nullifierModulus)\n      (fun a => TransferScalarAdditiveField01.actual_source_canonical_add_has_exact_mathematical_field_sum a a)')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarInputSemantics01.lean').write_bytes(source.encode())
for name in ['prepare_recipe.py','prepare_from01.py','prepare_from02.py']:(ROOT/name).write_bytes((old/name).read_bytes())
prep=(old/'prepare.py').read_text().replace("POOL=DIAG/'transfer-scalar-input-semantics-owned-floor-20261012-03'","POOL=DIAG/'transfer-scalar-input-semantics-owned-floor-20261012-04'")
before="'imports':['ShielddSecurity.TransferScalarAdditiveField01']";assert prep.count(before)==1
prep=prep.replace(before,"'imports':['ShielddSecurity.TransferScalarAdditiveField01','ShielddSecurity.TransferScalarFieldValues01']")
extra="""failed_second=DIAG/'transfer-scalar-input-semantics-20261012-03'
assert json.loads((failed_second/'events.jsonl').read_text().splitlines()[-1])['result']['status']=='failed'
plan['pins'] += [pin(p) for p in sorted(failed_second.rglob('*')) if p.is_file()]+[pin(ROOT/'prepare_from03.py')]
"""
at=prep.index("plan['artifact_policy']");prep=prep[:at]+extra+prep[at:]
(ROOT/'prepare.py').write_bytes(prep.encode())
print({'same7_statements':True,'repair':'explicit source/arithmetic operators for higher-order lifting and explicit qualified multiplication import','all_prior_failed_and_setup_histories_retained':True,'finite_guards_unchanged':True})
