from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-square-cross-20261011-01'
assert not (ROOT/'prepare.py').exists()
source=(OLD/'handwritten/TransferScalarSquareCross01.lean').read_text()
needle='        Nat.mul_zero, Nat.add_zero]\n';assert source.count(needle)==1
source=source.replace(needle,needle+'      exact ⟨trivial, trivial⟩\n')
needle='          _ = _ := by rw [crossValue]; ac_rfl';assert source.count(needle)==1
source=source.replace(needle,'          _ = _ := by\n            change (packWords accumulated + multiplier.toNat * packWords (next :: rest)) + radix64 ^ 2 * crossValue (next :: rest) =\n              packWords accumulated + (multiplier.toNat * packWords (next :: rest) + radix64 ^ 2 * crossValue (next :: rest))\n            ac_rfl')
needle='  rw [contract.1, contract.2, Nat.zero_add]\n';assert source.count(needle)==1
source=source.replace(needle,needle+'  exact ⟨rfl, rfl⟩\n')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarSquareCross01.lean').write_text(source)
(ROOT/'context').mkdir();(ROOT/'context/scalar-square-cross-shape.json').write_bytes((OLD/'context/scalar-square-cross-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-square-cross-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-square-cross-owned-floor-20261011-02'")
at=s.index("plan['artifact_policy']")
extra="""failedSquareCross=DIAG/'transfer-scalar-square-cross-20261011-01'
plan['pins'] += [pin(failedSquareCross/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-square-cross-shape.json','handwritten/TransferScalarSquareCross01.lean','project/ShielddSecurity/TransferScalarSquareCross01.lean','runs/01-TransferScalarSquareCross01/stdout.txt']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'proof_only_repairs':3,'unchanged_source_definitions_and_contracts':True,'failed_raw_artifacts':11,'failed_credit':0})
