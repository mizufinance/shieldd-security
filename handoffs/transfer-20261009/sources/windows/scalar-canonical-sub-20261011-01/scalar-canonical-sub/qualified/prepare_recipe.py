from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-canonical-sub-20261011-01'
assert not (ROOT/'prepare.py').exists()
source=(OLD/'handwritten/TransferScalarCanonicalSub01.lean').read_text()
needle='  unfold sourceSubWords\n';assert source.count(needle)==1
source=source.replace(needle,'  dsimp only [sourceSubWords]\n')
needle='    rw [if_false, Nat.add_zero, Nat.mod_eq_of_lt differenceBound]';assert source.count(needle)==1
source=source.replace(needle,'    rw [if_neg (by decide : ¬ (false : Bool) = true), Nat.add_zero, Nat.mod_eq_of_lt differenceBound]')
needle='    rw [if_true]\n';assert source.count(needle)==1
source=source.replace(needle,'    rw [if_pos (rfl : (true : Bool) = true)]\n')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarCanonicalSub01.lean').write_text(source)
(ROOT/'context').mkdir();(ROOT/'context/scalar-canonical-sub-shape.json').write_bytes((OLD/'context/scalar-canonical-sub-shape.json').read_bytes())
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-scalar-canonical-sub-owned-floor-20261011-01'","POOL = DIAG / 'transfer-scalar-canonical-sub-owned-floor-20261011-02'")
at=s.index("plan['artifact_policy']")
extra="""failedSub=DIAG/'transfer-scalar-canonical-sub-20261011-01'
plan['pins'] += [pin(failedSub/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-canonical-sub-shape.json','handwritten/TransferScalarCanonicalSub01.lean','project/ShielddSecurity/TransferScalarCanonicalSub01.lean','runs/01-TransferScalarCanonicalSub01/stdout.txt']]
"""
s=s[:at]+extra+s[at:];(ROOT/'prepare.py').write_text(s)
print({'proof_only_repairs':3,'unchanged_source_definitions_and_contracts':True,'failed_raw_artifacts':11,'failed_credit':0})
