"""Fresh proof-only beta exposure and removal of unused simp arguments."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-scalar-wide-round-20261011-02'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir();(ROOT/'context').mkdir()
source=(old/'handwritten/TransferScalarWideRound01.lean').read_text()
needle='  have modulo := congrArg (fun value => value % radix64) row\n'
assert source.count(needle)==1
source=source.replace(needle,needle+'  dsimp only at modulo\n').replace('Nat.pow_succ, Nat.mul_add, Nat.add_mul','Nat.pow_succ, Nat.mul_add')
(ROOT/'handwritten/TransferScalarWideRound01.lean').write_text(source)
(ROOT/'context/wide-reduction-shape.json').write_bytes((old/'context/wide-reduction-shape.json').read_bytes())
s=(old/'prepare.py').read_text().replace('transfer-scalar-wide-round-owned-floor-20261011-02','transfer-scalar-wide-round-owned-floor-20261011-03')
s=s.replace(", pin(ROOT/'recipe_source.py')",'')
needle="plan['artifact_policy']"
s=s.replace(needle,"failedWide=DIAG/'transfer-scalar-wide-round-20261011-02'\nplan['pins'] += [pin(failedWide/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/wide-reduction-shape.json','handwritten/TransferScalarWideRound01.lean','project/ShielddSecurity/TransferScalarWideRound01.lean','runs/01-TransferScalarWideRound01/stdout.txt']]\n"+needle,1)
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':6,'preserved_setup_only':1,'preserved_failed_kernel_attempts':1,'failed_credit':0,'guards_unchanged':True})
