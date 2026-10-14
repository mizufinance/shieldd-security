import ShielddSecurity.TransferBlstArmInverseSmallApprox01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseLastingRow01
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseFirstMismatch01 (sourceFirstControlMismatch)

/-! UNRUN lasting signed small-component estimate after first mismatch.
Original input errors remain bounded at every prefix through31. A preserved
small approximation coordinate therefore yields a signed quotient component
of magnitude at most three error budgets, even after exchanges. Source width
identification, total bitlength progress and native word execution remain open. -/

theorem small_natural_approximation_and_error_bound_the_signed_actual_magnitude
    (actual : Int) (approx scale budget : Nat) (small : approx ≤ 2 * budget)
    (error : (actual - (scale : Int) * (approx : Int)).natAbs ≤ scale * budget) :
    actual.natAbs ≤ 3 * (scale * budget) := by
  have decomposition : actual = (actual - (scale : Int) * (approx : Int)) +
      (scale : Int) * (approx : Int) := by omega
  have triangle := Int.natAbs_add_le (actual - (scale : Int) * (approx : Int))
    ((scale : Int) * (approx : Int))
  have product : ((scale : Int) * (approx : Int)).natAbs = scale * approx := by
    rw [Int.natAbs_mul]
    rfl
  rw [←decomposition, product] at triangle
  have multiplied := Nat.mul_le_mul_left scale small
  rw [Nat.mul_left_comm scale 2] at multiplied
  omega

theorem a_small_natural_minimum_and_both_errors_bound_the_signed_actual_minimum
    (x y : Int) (p q scale budget : Nat) (small : min p q ≤ 2 * budget)
    (leftError : (x - (scale : Int) * (p : Int)).natAbs ≤ scale * budget)
    (rightError : (y - (scale : Int) * (q : Int)).natAbs ≤ scale * budget) :
    min x.natAbs y.natAbs ≤ 3 * (scale * budget) := by
  by_cases ordered : p ≤ q
  · rw [Nat.min_eq_left ordered] at small
    exact Nat.le_trans (Nat.min_le_left _ _)
      (small_natural_approximation_and_error_bound_the_signed_actual_magnitude x p scale budget small leftError)
  · have reversed : q ≤ p := by omega
    rw [Nat.min_eq_right reversed] at small
    exact Nat.le_trans (Nat.min_le_right _ _)
      (small_natural_approximation_and_error_bound_the_signed_actual_magnitude y q scale budget small rightError)

theorem original_first_mismatch_preserves_a_small_signed_quotient_component_through_prefix31
    (count remaining : Nat) (a b : SourceFourWords) (bounded : count < 31)
    (lastBound : count + 1 + remaining ≤ 31) (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approxA := sourceApproxLow31 windows.1 a.w0
    let approxB := sourceApproxLow31 windows.2 b.w0
    let approximate := sourceFactorInitial approxA approxB
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    let signed := sourceActualFactorQuotients (count + 1 + remaining) approxA approxB
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    sourceFirstControlMismatch count approximate actual →
      min signed.1.natAbs signed.2.natAbs ≤ 3 * 2 ^ (sourceFourWordWindowShift a b + 31) := by
  dsimp only
  intro first
  have small := TransferBlstArmInverseSmallApprox01.original_first_mismatch_preserves_a_small_natural_approximation_for_every_remaining_step
    count remaining a b bounded oddB first
  have budget : (2 : Nat) ^ 32 = 2 * 2147483648 := by decide +kernel
  rw [budget] at small
  have errors := TransferBlstArmInverseWindowError01.original_source_produced_four_word_windows_derive_both_factor_prefix_error_bounds
    (count + 1 + remaining) a b lastBound oddB
  have result := a_small_natural_minimum_and_both_errors_bound_the_signed_actual_minimum
    _ _ _ _ (2 ^ sourceFourWordWindowShift a b) 2147483648 small errors.1 errors.2
  have constant : (2 : Nat) ^ 31 = 2147483648 := by decide +kernel
  simpa only [Nat.pow_add, constant] using result

set_option pp.all true in
#check @small_natural_approximation_and_error_bound_the_signed_actual_magnitude
#print axioms small_natural_approximation_and_error_bound_the_signed_actual_magnitude
set_option pp.all true in
#check @a_small_natural_minimum_and_both_errors_bound_the_signed_actual_minimum
#print axioms a_small_natural_minimum_and_both_errors_bound_the_signed_actual_minimum
set_option pp.all true in
#check @original_first_mismatch_preserves_a_small_signed_quotient_component_through_prefix31
#print axioms original_first_mismatch_preserves_a_small_signed_quotient_component_through_prefix31
end ShielddSecurity.TransferBlstArmInverseLastingRow01
