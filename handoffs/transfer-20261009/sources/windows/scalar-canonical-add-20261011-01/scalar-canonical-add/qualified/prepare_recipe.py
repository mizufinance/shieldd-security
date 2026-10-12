from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-canonical-add-20261011-01'
assert not (ROOT/'prepare.py').exists()
source=(OLD/'handwritten/TransferScalarCanonicalAdd01.lean').read_text()
needle='    rw [Vector.length_toList, Vector.length_toList]\n'
assert source.count(needle)==2
source=source.replace(needle,needle+'    exact Nat.le_refl 4\n')
needle='      rw [decomposition, Nat.add_mod_right, Nat.mod_eq_of_lt differenceBound]\n'
assert source.count(needle)==1
source=source.replace(needle,needle+'      exact Nat.add_sub_cancel _ _\n')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarCanonicalAdd01.lean').write_text(source)
(ROOT/'context').mkdir();(ROOT/'context/scalar-canonical-add-shape.json').write_bytes((OLD/'context/scalar-canonical-add-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-canonical-add-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-canonical-add-owned-floor-20261011-02'")
at=s.index("plan['artifact_policy']")
extra="""failedAdd=DIAG/'transfer-scalar-canonical-add-20261011-01'
plan['pins'] += [pin(failedAdd/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-canonical-add-shape.json','handwritten/TransferScalarCanonicalAdd01.lean','project/ShielddSecurity/TransferScalarCanonicalAdd01.lean','runs/01-TransferScalarCanonicalAdd01/stdout.txt']]
"""
s=s[:at]+extra+s[at:]
(ROOT/'prepare.py').write_text(s)
print({'proof_only_repairs':3,'unchanged_source_definitions_and_contracts':True,'failed_raw_artifacts':11,'failed_credit':0})
