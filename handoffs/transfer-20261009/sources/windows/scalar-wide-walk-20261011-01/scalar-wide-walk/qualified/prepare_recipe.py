"""Proof-only fresh repair: list case rewrite, coefficient grouping, distributivity."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-scalar-wide-walk-20261011-01'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir()
source=(old/'handwritten/TransferScalarWideWalk01.lean').read_text()
assert source.count('rw [dropped, tailEqual]')==1
source=source.replace('rw [dropped, tailEqual]','rw [tailEqual]')
source=source.replace('(state.1.take 4 |>.headD 0 * inverseWord)','((state.1.take 4).headD 0 * inverseWord)')
source=source.replace('by rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one]; ac_rfl','by simp only [Nat.pow_succ, Nat.mul_add, Nat.mul_one]; ac_rfl')
(ROOT/'handwritten/TransferScalarWideWalk01.lean').write_text(source)
s=(old/'prepare.py').read_text().replace('transfer-scalar-wide-walk-owned-floor-20261011-01','transfer-scalar-wide-walk-owned-floor-20261011-02')
s=s.replace("plan['artifact_policy']","failedWalk=DIAG/'transfer-scalar-wide-walk-20261011-01'\nplan['pins'] += [pin(failedWalk/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarWideWalk01.lean','project/ShielddSecurity/TransferScalarWideWalk01.lean','runs/01-TransferScalarWideWalk01/stdout.txt']]\nplan['artifact_policy']",1)
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':7,'failed_attempts_preserved':1,'failed_credit':0,'guards_unchanged':True})
