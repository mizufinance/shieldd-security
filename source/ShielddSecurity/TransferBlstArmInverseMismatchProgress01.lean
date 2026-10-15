import ShielddSecurity.TransferBlstArmInversePairPowerProgress01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseMismatchProgress01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords sourceSecondWindowChoice)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)
open TransferBlstArmInverseFactors01 (sourceFactorInitial)
open TransferBlstArmInverseFirstMismatch01 (sourceFirstControlMismatch)
open TransferBlstArmInverseErrorRows01 (sourceActualFactorQuotients)
open TransferBlstArmInverseFullWidth01 (sourceClippedJointBitwidth)
open TransferBlstArmInverseBitlengthBudget01 (sourceNatBitlength)

/-! Original first control mismatch derives a decrease of at least31 in
the sum of exact bitlengths of the two full signed output magnitudes. No
chosen initial width, minimum, comparison parity or error observation is
supplied. The all-controls-synchronized case, iteration and native bridge
remain distinct obligations. -/

theorem original_nonzero_upper_window_has_a_positive_full_input_shift
    (a b : SourceFourWords)
    (nonzero : (sourceSecondWindowChoice a b).highA ||| (sourceSecondWindowChoice a b).highB ≠ 0) :
    0 < sourceFourWordWindowShift a b := by
  have count := TransferBlstArmInverseFullWindowBounds01.original_nonzero_raw_joint_clz_count_is_strictly_below64 _ _ nonzero
  have retained := TransferBlstArmInverseWindowJoint01.original_nonzero_joint_high_window_retains_the_selected_high_words_and_raw_clz
    (sourceSecondWindowChoice a b).highA (sourceSecondWindowChoice a b).highB
    (sourceSecondWindowChoice a b).lowA (sourceSecondWindowChoice a b).lowB nonzero
  unfold sourceFourWordWindowShift
  rw [if_neg nonzero, retained]
  change 0 < 64 * ((sourceSecondWindowChoice a b).index - 1) +
    (64 - ((sourceSecondWindowChoice a b).highA ||| (sourceSecondWindowChoice a b).highB).toBitVec.clz.toNat)
  omega

theorem original_nonzero_upper_window_and_positive_inputs_identify_the_exact_joint_bitlength
    (a b : SourceFourWords)
    (nonzero : (sourceSecondWindowChoice a b).highA ||| (sourceSecondWindowChoice a b).highB ≠ 0)
    (positiveA : 0 < sourcePackedFourWords a) (positiveB : 0 < sourcePackedFourWords b) :
    sourceClippedJointBitwidth a b =
      sourceNatBitlength (max (sourcePackedFourWords a) (sourcePackedFourWords b)) := by
  have shift := original_nonzero_upper_window_has_a_positive_full_input_shift a b nonzero
  have width := TransferBlstArmInverseFullWidth01.original_computed_shift_plus64_is_the_exact_clipped_full_input_joint_bitwidth a b
  have innerLower : 64 ≤ max ((sourcePackedFourWords a).log2 + 1) ((sourcePackedFourWords b).log2 + 1) := by
    by_contra no
    have smaller : max ((sourcePackedFourWords a).log2 + 1) ((sourcePackedFourWords b).log2 + 1) ≤ 64 := by omega
    simp only [sourceClippedJointBitwidth, Nat.max_eq_left smaller] at width
    omega
  rw [sourceClippedJointBitwidth, Nat.max_eq_right innerLower]
  by_cases order : sourcePackedFourWords a ≤ sourcePackedFourWords b
  · rw [Nat.max_eq_right order]
    have bits := TransferBlstArmInverseBitlengthBudget01.the_exact_bitlength_is_monotone _ _ order
    simp only [sourceNatBitlength, if_neg (Nat.ne_of_gt positiveA), if_neg (Nat.ne_of_gt positiveB)] at bits ⊢
    exact Nat.max_eq_right bits
  · have reverse : sourcePackedFourWords b ≤ sourcePackedFourWords a := by omega
    rw [Nat.max_eq_left reverse]
    have bits := TransferBlstArmInverseBitlengthBudget01.the_exact_bitlength_is_monotone _ _ reverse
    simp only [sourceNatBitlength, if_neg (Nat.ne_of_gt positiveA), if_neg (Nat.ne_of_gt positiveB)] at bits ⊢
    exact Nat.max_eq_left bits

theorem original_first_control_mismatch_decreases_the_full_pair_bitlength_by_at_least31
    (count : Nat) (a b : SourceFourWords) (bounded : count < 31) (oddB : b.w0.toNat % 2 = 1)
    (first : sourceFirstControlMismatch count
      (sourceFactorInitial (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
        (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0))
      (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))) :
    let final := sourceActualFactorQuotients 31
      (sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0)
      (sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0)
      (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int)
    sourceNatBitlength final.1.natAbs + sourceNatBitlength final.2.natAbs + 31 ≤
      sourceNatBitlength (sourcePackedFourWords a) + sourceNatBitlength (sourcePackedFourWords b) := by
  dsimp only
  have nonzero := TransferBlstArmInverseMismatchOperands01.original_first_control_mismatch_requires_a_nonzero_upper_window count a b first
  have lower := TransferBlstArmInverseMismatchOperands01.original_first_control_mismatch_requires_both_full_inputs_at_least_the_error_budget count a b bounded oddB first
  have small := TransferBlstArmInverseSharpLasting01.original_first_mismatch_final_small_component_is_bounded_at_full_width_minus33 count a b bounded oddB first
  have large := TransferBlstArmInverseMismatchMaximum01.original_first_mismatch_final_signed_maximum_is_bounded_by_the_initial_minimum_plus_two_budgets count a b bounded oddB first
  have width := TransferBlstArmInverseFullWidth01.original_computed_shift_plus64_is_the_exact_clipped_full_input_joint_bitwidth a b
  have smallExponent : sourceClippedJointBitwidth a b - 33 = sourceFourWordWindowShift a b + 31 := by omega
  have largeExponent : sourceClippedJointBitwidth a b - 32 = sourceFourWordWindowShift a b + 32 := by omega
  have constant : (2 : Nat) ^ 31 = 2147483648 := by decide +kernel
  have lowerPower : 2 ^ (sourceClippedJointBitwidth a b - 33) ≤ min (sourcePackedFourWords a) (sourcePackedFourWords b) := by
    simpa only [smallExponent, Nat.pow_add, constant] using lower
  rw [←largeExponent] at large
  have result := TransferBlstArmInversePairPowerProgress01.sharp_minimum_and_maximum_bounds_decrease_the_total_pair_bitlength_by31
    _ _ _ (sourceClippedJointBitwidth a b) (by omega) lowerPower small large
  have positiveMinimum := Nat.lt_of_lt_of_le (Nat.two_pow_pos _) lowerPower
  have positiveA : 0 < sourcePackedFourWords a := Nat.lt_of_lt_of_le positiveMinimum (Nat.min_le_left _ _)
  have positiveB : 0 < sourcePackedFourWords b := Nat.lt_of_lt_of_le positiveMinimum (Nat.min_le_right _ _)
  have exactWidth := original_nonzero_upper_window_and_positive_inputs_identify_the_exact_joint_bitlength a b nonzero positiveA positiveB
  rw [exactWidth] at result
  rw [TransferBlstArmInverseBitlengthBudget01.the_sum_of_exact_pair_bitlengths_equals_the_sum_for_the_minimum_and_maximum
    (sourcePackedFourWords a) (sourcePackedFourWords b)]
  simpa only [Nat.add_comm] using result

set_option pp.all true in
#check @original_nonzero_upper_window_has_a_positive_full_input_shift
#print axioms original_nonzero_upper_window_has_a_positive_full_input_shift
set_option pp.all true in
#check @original_nonzero_upper_window_and_positive_inputs_identify_the_exact_joint_bitlength
#print axioms original_nonzero_upper_window_and_positive_inputs_identify_the_exact_joint_bitlength
set_option pp.all true in
#check @original_first_control_mismatch_decreases_the_full_pair_bitlength_by_at_least31
#print axioms original_first_control_mismatch_decreases_the_full_pair_bitlength_by_at_least31
end ShielddSecurity.TransferBlstArmInverseMismatchProgress01
