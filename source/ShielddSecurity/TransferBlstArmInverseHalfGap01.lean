import ShielddSecurity.TransferBlstArmInverseFirstParity01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseHalfGap01
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseFirstMismatch01 (sourceFirstControlMismatch)

/-! UNRUN first-mismatch development. An even upper budget bounds the signed
half-gap even when Euclidean division rounds a negative odd gap down. This is
only the mathematical half-gap: identification with the next controlled row
quotient and post-mismatch lasting behavior remain separate obligations. -/

theorem symbolic_signed_gap_bounded_by_two_budgets_derives_the_half_gap_bound
    (gap : Int) (budget : Nat) (bounded : gap.natAbs ≤ 2 * budget) :
    (gap / 2).natAbs ≤ budget := by
  have both := TransferBlstArmInverseOrderGap01.signed_error_natabs_bound_derives_both_integer_budget_bounds
    gap (2 * budget) bounded
  by_cases nonnegative : 0 ≤ gap / 2
  · have value := Int.eq_natAbs_of_nonneg nonnegative
    omega
  · have value := Int.eq_neg_natAbs_of_nonpos (show gap / 2 ≤ 0 by omega)
    omega

theorem original_first_mismatch_budget_is_exactly_twice_the_half_gap_budget
    (shift : Nat) : 2 ^ (shift + 32) = 2 * 2 ^ (shift + 31) := by
  have split : shift + 32 = (shift + 31) + 1 := by omega
  rw [split, Nat.pow_succ, Nat.mul_comm]

theorem original_source_first_control_mismatch_derives_the_signed_half_gap_bound
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31) (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approximate := sourceFactorInitial
      (sourceApproxLow31 windows.1 a.w0) (sourceApproxLow31 windows.2 b.w0)
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    sourceFirstControlMismatch count approximate actual →
    ((((sourceFactorWalk count actual).a : Int) - ((sourceFactorWalk count actual).b : Int)) / 2).natAbs ≤
      2 ^ (sourceFourWordWindowShift a b + 31) := by
  dsimp only
  intro first
  have gap := TransferBlstArmInverseFirstParity01.original_source_first_control_mismatch_derives_the_exact_loop_gap_without_a_parity_premise
    count a b bounded oddB first
  rw [original_first_mismatch_budget_is_exactly_twice_the_half_gap_budget] at gap
  exact symbolic_signed_gap_bounded_by_two_budgets_derives_the_half_gap_bound _ _ gap

set_option pp.all true in
#check @symbolic_signed_gap_bounded_by_two_budgets_derives_the_half_gap_bound
#print axioms symbolic_signed_gap_bounded_by_two_budgets_derives_the_half_gap_bound
set_option pp.all true in
#check @original_first_mismatch_budget_is_exactly_twice_the_half_gap_budget
#print axioms original_first_mismatch_budget_is_exactly_twice_the_half_gap_budget
set_option pp.all true in
#check @original_source_first_control_mismatch_derives_the_signed_half_gap_bound
#print axioms original_source_first_control_mismatch_derives_the_signed_half_gap_bound
end ShielddSecurity.TransferBlstArmInverseHalfGap01
