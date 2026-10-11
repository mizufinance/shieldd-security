"""Expose named radix64 bound without changing the six contracts."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-scalar-wide-round-20261011-03'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir();(ROOT/'context').mkdir()
source=(old/'handwritten/TransferScalarWideRound01.lean').read_text()
needle='  rw [Nat.add_mul_mod_self_left,\n    Nat.mod_eq_of_lt ((macLoop (low.headD 0 * inverseWord) 0 (low.zip modulusWords)).1.headD 0).toNat_lt,'
assert source.count(needle)==1
source=source.replace(needle,'  have lowBound : ((macLoop (low.headD 0 * inverseWord) 0 (low.zip modulusWords)).1.headD 0).toNat < radix64 :=\n    ((macLoop (low.headD 0 * inverseWord) 0 (low.zip modulusWords)).1.headD 0).toNat_lt\n  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lowBound,')
(ROOT/'handwritten/TransferScalarWideRound01.lean').write_text(source)
(ROOT/'context/wide-reduction-shape.json').write_bytes((old/'context/wide-reduction-shape.json').read_bytes())
s=(old/'prepare.py').read_text().replace('transfer-scalar-wide-round-owned-floor-20261011-03','transfer-scalar-wide-round-owned-floor-20261011-04')
s=s.replace("plan['artifact_policy']","failedWide03=DIAG/'transfer-scalar-wide-round-20261011-03'\nplan['pins'] += [pin(failedWide03/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/wide-reduction-shape.json','handwritten/TransferScalarWideRound01.lean','project/ShielddSecurity/TransferScalarWideRound01.lean','runs/01-TransferScalarWideRound01/stdout.txt']]\nplan['artifact_policy']",1)
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':6,'preserved_setup_only':1,'preserved_failed_kernel_attempts':2,'failed_credit':0,'guards_unchanged':True})
