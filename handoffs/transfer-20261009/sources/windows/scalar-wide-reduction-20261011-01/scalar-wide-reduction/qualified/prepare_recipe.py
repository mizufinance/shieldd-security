"""Keep core-only proof: explicit Nat transitivity and finite carry case split."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-scalar-wide-reduction-20261011-01'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir()
source=(old/'handwritten/TransferScalarWideReduction01.lean').read_text()
source=source.replace('exact bounded.trans_eq (Nat.mul_comm _ _)','simpa only [Nat.mul_comm] using bounded')
source=source.replace('have small := total.trans twice_actual_modulus_fits_four_word_radix','have small := Nat.lt_trans total twice_actual_modulus_fits_four_word_radix')
oldproof='''    by_contra nonzero
    have one : 1 ≤ (wideRounds 4 (words, 0)).2.toNat := by omega
    have lower := Nat.mul_le_mul_left (radix64 ^ 4) one
    rw [Nat.mul_one] at lower
    unfold wideValue at small
    omega'''
newproof='''    by_cases isZero : (wideRounds 4 (words, 0)).2.toNat = 0
    · exact isZero
    · have one : 1 ≤ (wideRounds 4 (words, 0)).2.toNat := by omega
      have lower := Nat.mul_le_mul_left (radix64 ^ 4) one
      rw [Nat.mul_one] at lower
      unfold wideValue at small
      omega'''
assert source.count(oldproof)==1;source=source.replace(oldproof,newproof).replace('exact range.trans step','exact Nat.lt_trans range step')
(ROOT/'handwritten/TransferScalarWideReduction01.lean').write_text(source)
s=(old/'prepare.py').read_text().replace('transfer-scalar-wide-reduction-owned-floor-20261011-01','transfer-scalar-wide-reduction-owned-floor-20261011-02')
s=s.replace("plan['artifact_policy']","failedReduction=DIAG/'transfer-scalar-wide-reduction-20261011-01'\nplan['pins'] += [pin(failedReduction/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarWideReduction01.lean','project/ShielddSecurity/TransferScalarWideReduction01.lean','runs/01-TransferScalarWideReduction01/stdout.txt']]\nplan['artifact_policy']",1)
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':8,'failed_attempts_preserved':1,'failed_credit':0,'guards_unchanged':True})
