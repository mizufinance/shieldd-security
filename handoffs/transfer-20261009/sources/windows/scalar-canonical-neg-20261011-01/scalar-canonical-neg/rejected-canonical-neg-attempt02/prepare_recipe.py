from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-canonical-neg-20261011-01'
assert not (ROOT/'prepare.py').exists()
source=(OLD/'handwritten/TransferScalarCanonicalNeg01.lean').read_text()
old='        have head := Nat.eq_zero_of_add_eq_zero_left zero\n        have product := Nat.eq_zero_of_add_eq_zero_right zero\n        have tail : packWords rest = 0 := (Nat.mul_eq_zero.mp product).resolve_left (by decide)'
new='        have head : word.toNat = 0 := by omega\n        have product : radix64 * packWords rest = 0 := by omega\n        have tail : packWords rest = 0 := (Nat.mul_eq_zero.mp product).resolve_left (by decide : radix64 ≠ 0)'
assert source.count(old)==1;source=source.replace(old,new)
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarCanonicalNeg01.lean').write_text(source)
(ROOT/'context').mkdir();(ROOT/'context/scalar-canonical-neg-shape.json').write_bytes((OLD/'context/scalar-canonical-neg-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-canonical-neg-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-canonical-neg-owned-floor-20261011-02'")
at=s.index("plan['artifact_policy']")
extra="""failedNeg=DIAG/'transfer-scalar-canonical-neg-20261011-01'
plan['pins'] += [pin(failedNeg/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-canonical-neg-shape.json','handwritten/TransferScalarCanonicalNeg01.lean','project/ShielddSecurity/TransferScalarCanonicalNeg01.lean','runs/01-TransferScalarCanonicalNeg01/stdout.txt']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'proof_only_repair':'explicit zero-summand and zero-product types','unchanged_source_definitions_and_contracts':True,'failed_raw_artifacts':11,'failed_credit':0})
