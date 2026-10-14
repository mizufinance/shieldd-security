import ShielddSecurity.TransferBlstArmInverseMinWalk01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseSmallApprox01
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseFirstMismatch01 (sourceFirstControlMismatch)

/-! UNRUN lasting small natural approximation after a first mismatch. The
first next quotient is bounded from original inputs; its existing error
bound derives a small approximation coordinate. The source recurrence then
preserves a small coordinate for every remaining symbolic step. Signed full
quotient magnitude, bitlength progress and native execution remain separate. -/

theorem bounded_actual_value_and_scaled_error_derive_a_small_natural_approximation
    (actual : Int) (approx scale budget : Nat) (positive : 0 < scale)
    (small : actual.natAbs ≤ scale * budget)
    (error : (actual - (scale : Int) * (approx : Int)).natAbs ≤ scale * budget) :
    approx ≤ 2 * budget := by
  have smallBounds := TransferBlstArmInverseOrderGap01.signed_error_natabs_bound_derives_both_integer_budget_bounds
    actual (scale * budget) small
  have errorBounds := TransferBlstArmInverseOrderGap01.signed_error_natabs_bound_derives_both_integer_budget_bounds
    (actual - (scale : Int) * (approx : Int)) (scale * budget) error
  simp only [Int.natCast_mul] at smallBounds errorBounds
  have multiplied : (scale : Int) * (approx : Int) ≤ (scale : Int) * (2 * (budget : Int)) := by
    rw [Int.mul_left_comm (scale : Int) 2]
    omega
  have ordered := Int.le_of_mul_le_mul_left multiplied (show 0 < (scale : Int) by omega)
  omega

theorem original_first_mismatch_next_natural_approximation_is_at_most_two_to_32
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31)
    (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approximate := sourceFactorInitial
      (sourceApproxLow31 windows.1 a.w0) (sourceApproxLow31 windows.2 b.w0)
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    sourceFirstControlMismatch count approximate actual →
      (sourceFactorWalk (count + 1) approximate).a ≤ 2 ^ 32 := by
  dsimp only
  intro first
  have small := TransferBlstArmInverseNextRow01.original_first_mismatch_next_controlled_quotient_has_the_derived_half_gap_bound
    count a b bounded oddB first
  have constant : (2 : Nat) ^ 31 = 2147483648 := by decide +kernel
  rw [Nat.pow_add, constant] at small
  have errors := TransferBlstArmInverseWindowError01.original_source_produced_four_word_windows_derive_both_factor_prefix_error_bounds
    (count + 1) a b (by omega) oddB
  have result := bounded_actual_value_and_scaled_error_derive_a_small_natural_approximation
    _ _ (2 ^ sourceFourWordWindowShift a b) 2147483648
    (Nat.two_pow_pos _) small errors.1
  have exactBudget : 2 * 2147483648 = (2 : Nat) ^ 32 := by decide +kernel
  rw [exactBudget] at result
  exact result

theorem original_first_mismatch_preserves_a_small_natural_approximation_for_every_remaining_step
    (count remaining : Nat) (a b : SourceFourWords) (bounded : count < 31)
    (oddB : b.w0.toNat % 2 = 1) :
    let windows := sourceFourWordWindowWords a b
    let approximate := sourceFactorInitial
      (sourceApproxLow31 windows.1 a.w0) (sourceApproxLow31 windows.2 b.w0)
    let actual := sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b)
    sourceFirstControlMismatch count approximate actual →
      min (sourceFactorWalk (count + 1 + remaining) approximate).a
        (sourceFactorWalk (count + 1 + remaining) approximate).b ≤ 2 ^ 32 := by
  dsimp only
  intro first
  have small := original_first_mismatch_next_natural_approximation_is_at_most_two_to_32
    count a b bounded oddB first
  rw [TransferBlstArmInverseMinWalk01.symbolic_original_factor_walk_composes_at_any_prefix]
  exact Nat.le_trans
    (TransferBlstArmInverseMinWalk01.every_symbolic_factor_walk_preserves_its_initial_natural_minimum_bound _ _)
    (Nat.le_trans (Nat.min_le_left _ _) small)

set_option pp.all true in
#check @bounded_actual_value_and_scaled_error_derive_a_small_natural_approximation
#print axioms bounded_actual_value_and_scaled_error_derive_a_small_natural_approximation
set_option pp.all true in
#check @original_first_mismatch_next_natural_approximation_is_at_most_two_to_32
#print axioms original_first_mismatch_next_natural_approximation_is_at_most_two_to_32
set_option pp.all true in
#check @original_first_mismatch_preserves_a_small_natural_approximation_for_every_remaining_step
#print axioms original_first_mismatch_preserves_a_small_natural_approximation_for_every_remaining_step
end ShielddSecurity.TransferBlstArmInverseSmallApprox01
