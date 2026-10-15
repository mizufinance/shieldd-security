import ShielddSecurity.TransferBlstArmInverseInitialOperands01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseMismatchOperands01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords sourceSecondWindowChoice)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseFirstMismatch01 (sourceFirstControlMismatch)

/-! First source control disagreement forces both original full operands to
be at least the scaled low31 error budget. All window and initial-size
premises derive from the original words. This is source mathematics; native
execution and the total pair bitlength decrease remain separate. -/

theorem original_first_control_mismatch_requires_a_nonzero_upper_window
    (count : Nat) (a b : SourceFourWords)
    (first : sourceFirstControlMismatch count
      (sourceFactorInitial (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
        (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))
      (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))) :
    (sourceSecondWindowChoice a b).highA ||| (sourceSecondWindowChoice a b).highB ≠ 0 := by
  intro zero
  have fallback := TransferBlstArmInverseInitialOperands01.original_zero_upper_window_returns_both_full_initial_approximations a b zero
  rw [fallback.1, fallback.2] at first
  exact first.2 rfl

theorem original_first_control_mismatch_requires_both_initial_approximations_at_least_two31
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31) (oddB : b.w0.toNat % 2 = 1)
    (first : sourceFirstControlMismatch count
      (sourceFactorInitial (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
        (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))
      (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))) :
    2 ^ 31 ≤ min (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0) := by
  have nonzero := original_first_control_mismatch_requires_a_nonzero_upper_window count a b first
  have large := TransferBlstArmInverseInitialOperands01.original_nonzero_upper_window_derives_a_large_initial_approximation_sum a b nonzero
  have odd := TransferBlstArmInverseApproxBits01.original_low31_approximation_preserves_oddness_of_the_original_low_word
    (sourceFourWordWindowWords a b).2 b.w0 oddB
  have gap := TransferBlstArmInverseApproxOrderBudget01.original_first_control_mismatch_derives_the_approximation_gap_at_most_two_to32
    count a b bounded oddB first
  by_contra no
  have small : min (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0) < 2 ^ 31 := by omega
  have separation := TransferBlstArmInverseNaturalScale01.large_initial_approximation_sum_and_small_minimum_force_separation_before31
    count (sourceFactorInitial (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)) bounded odd large small
  omega

theorem original_first_control_mismatch_requires_both_full_inputs_at_least_the_error_budget
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31) (oddB : b.w0.toNat % 2 = 1)
    (first : sourceFirstControlMismatch count
      (sourceFactorInitial (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
        (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))
      (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))) :
    2 ^ sourceFourWordWindowShift a b * 2147483648 ≤ min (sourcePackedFourWords a) (sourcePackedFourWords b) := by
  have approximateLower := original_first_control_mismatch_requires_both_initial_approximations_at_least_two31 count a b bounded oddB first
  have producer := TransferBlstArmInverseWindowInput01.original_source_window_words_derive_the_high_window_premises_for_both_entire_inputs a b
  apply Nat.le_min_of_le_of_le
  · by_contra no
    have small : sourcePackedFourWords a < 2 ^ sourceFourWordWindowShift a b * 2147483648 := by omega
    have smallApprox := TransferBlstArmInverseInitialOperands01.a_full_input_below_the_scaled_low31_budget_has_a_small_initial_approximation
      _ _ _ a.w0 producer.1 small
    have minimum := Nat.min_le_left (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
    omega
  · by_contra no
    have small : sourcePackedFourWords b < 2 ^ sourceFourWordWindowShift a b * 2147483648 := by omega
    have smallApprox := TransferBlstArmInverseInitialOperands01.a_full_input_below_the_scaled_low31_budget_has_a_small_initial_approximation
      _ _ _ b.w0 producer.2 small
    have minimum := Nat.min_le_right (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
    omega

set_option pp.all true in
#check @original_first_control_mismatch_requires_a_nonzero_upper_window
#print axioms original_first_control_mismatch_requires_a_nonzero_upper_window
set_option pp.all true in
#check @original_first_control_mismatch_requires_both_initial_approximations_at_least_two31
#print axioms original_first_control_mismatch_requires_both_initial_approximations_at_least_two31
set_option pp.all true in
#check @original_first_control_mismatch_requires_both_full_inputs_at_least_the_error_budget
#print axioms original_first_control_mismatch_requires_both_full_inputs_at_least_the_error_budget
end ShielddSecurity.TransferBlstArmInverseMismatchOperands01
