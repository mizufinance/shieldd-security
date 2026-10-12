from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-square-diagonal-20261011-03'
assert not (ROOT/'prepare.py').exists()
source=(OLD/'handwritten/TransferScalarSquareDiagonal01.lean').read_text()
needle='        rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_add]';assert source.count(needle)==1
source=source.replace(needle,'        simp only [Nat.add_mul, Nat.one_mul]')
needle='        change second.1.toNat + radix64 * second.2.toNat = high.toNat + first.2.toNat at secondValue';assert source.count(needle)==1
source=source.replace(needle,'        rw [UInt64.toNat_zero, Nat.zero_add] at secondValue\n'+needle)
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarSquareDiagonal01.lean').write_text(source)
(ROOT/'context').mkdir();(ROOT/'context/scalar-square-diagonal-shape.json').write_bytes((OLD/'context/scalar-square-diagonal-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-square-diagonal-owned-floor-20261011-03'","POOL = DIAG / 'transfer-scalar-square-diagonal-owned-floor-20261011-04'")
at=s.index("plan['artifact_policy']")
extra="""failedDiagonal=DIAG/'transfer-scalar-square-diagonal-20261011-03'
plan['pins'] += [pin(failedDiagonal/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-square-diagonal-shape.json','handwritten/TransferScalarSquareDiagonal01.lean','project/ShielddSecurity/TransferScalarSquareDiagonal01.lean','runs/01-TransferScalarSquareDiagonal01/stdout.txt']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'proof_only_repairs':2,'unchanged_definitions_and_contracts':True,'prior_raw_artifacts':29})
