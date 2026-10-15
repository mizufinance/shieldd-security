import ShielddSecurity.TransferBlstArmInverseApproxOrderBudget01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseInitialOperands01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords sourceSecondWindowChoice)
open TransferBlstArmInverseWindowInput01 (sourceFourWordWindowWords sourceFourWordWindowShift)
open TransferBlstArmInverseApproxBits01 (sourceApproxLow31)

/-! Initial operand bounds derived from the original source window producer.
The nonzero upper window supplies a large approximation sum. A full operand
below the low31 error budget supplies a small approximation. Zero-window
fallback returns both full inputs exactly. Native execution remains open. -/

theorem a_high_word_at_least_two63_retains_that_lower_bound_after_low31_replacement
    (high low : UInt64) (large : 2 ^ 63 ≤ high.toNat) :
    2 ^ 63 ≤ sourceApproxLow31 high low := by
  unfold sourceApproxLow31
  have remainder := Nat.mod_lt high.toNat (show 0 < 2147483648 by decide)
  have decomposition := Nat.mod_add_div high.toNat 2147483648
  omega

theorem a_full_input_below_the_scaled_low31_budget_has_a_small_initial_approximation
    (input shift : Nat) (high low : UInt64)
    (producer : high.toNat = input / 2 ^ shift)
    (small : input < 2 ^ shift * 2147483648) :
    sourceApproxLow31 high low < 2 ^ 31 := by
  have quotient : input / 2 ^ shift < 2147483648 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos shift)).2 (by simpa only [Nat.mul_comm] using small)
  have highSmall : high.toNat < 2147483648 := by rw [producer]; exact quotient
  unfold sourceApproxLow31
  rw [Nat.div_eq_of_lt highSmall, Nat.zero_mul, Nat.zero_add]
  exact Nat.mod_lt _ (by decide)

theorem original_nonzero_upper_window_derives_a_large_initial_approximation_sum
    (a b : SourceFourWords)
    (nonzero : (sourceSecondWindowChoice a b).highA ||| (sourceSecondWindowChoice a b).highB ≠ 0) :
    2 ^ 63 ≤ sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0 +
      sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0 := by
  have lower := TransferBlstArmInverseFullWindowBounds01.original_nonzero_selected_upper_window_derives_a_full_input_lower_power a b nonzero
  have producer := TransferBlstArmInverseWindowInput01.original_source_window_words_derive_the_high_window_premises_for_both_entire_inputs a b
  have exponent : 2 ^ (sourceFourWordWindowShift a b + 63) = 2 ^ 63 * 2 ^ sourceFourWordWindowShift a b := by
    rw [Nat.pow_add, Nat.mul_comm]
  rw [exponent] at lower
  rcases lower with left | right
  · have high : 2 ^ 63 ≤ (sourceFourWordWindowWords a b).1.toNat := by
      rw [producer.1]
      exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 left
    have retained := a_high_word_at_least_two63_retains_that_lower_bound_after_low31_replacement _ a.w0 high
    omega
  · have high : 2 ^ 63 ≤ (sourceFourWordWindowWords a b).2.toNat := by
      rw [producer.2]
      exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 right
    have retained := a_high_word_at_least_two63_retains_that_lower_bound_after_low31_replacement _ b.w0 high
    omega

theorem equal_high_and_low_word_values_make_low31_replacement_exact
    (high low : UInt64) (equal : high.toNat = low.toNat) :
    sourceApproxLow31 high low = low.toNat := by
  unfold sourceApproxLow31
  rw [equal, Nat.add_comm, Nat.mul_comm]
  exact Nat.mod_add_div _ _

theorem original_zero_upper_window_returns_both_full_initial_approximations
    (a b : SourceFourWords)
    (zero : (sourceSecondWindowChoice a b).highA ||| (sourceSecondWindowChoice a b).highB = 0) :
    sourceApproxLow31 (sourceFourWordWindowWords a b).1 a.w0 = sourcePackedFourWords a ∧
      sourceApproxLow31 (sourceFourWordWindowWords a b).2 b.w0 = sourcePackedFourWords b := by
  have all := (TransferBlstArmInverseWindowJoint01.original_selected_joint_window_is_zero_exactly_when_all_original_upper_joint_words_are_zero a b).mp zero
  have top := UInt64.or_eq_zero_iff.mp all.1
  have middle := UInt64.or_eq_zero_iff.mp all.2.1
  have lower := UInt64.or_eq_zero_iff.mp all.2.2
  have left := TransferBlstArmInverseWindowSelect01.original_all_zero_upper_words_reduce_the_entire_packed_input_to_its_low_word a lower.1 middle.1 top.1
  have right := TransferBlstArmInverseWindowSelect01.original_all_zero_upper_words_reduce_the_entire_packed_input_to_its_low_word b lower.2 middle.2 top.2
  have producer := TransferBlstArmInverseWindowInput01.original_source_window_words_derive_the_high_window_premises_for_both_entire_inputs a b
  have shift := TransferBlstArmInverseFullWindowBounds01.original_zero_selected_upper_window_has_exactly_zero_source_shift a b zero
  simp only [shift, Nat.pow_zero, Nat.div_one, left, right] at producer
  constructor
  · rw [left]
    exact equal_high_and_low_word_values_make_low31_replacement_exact _ _ producer.1
  · rw [right]
    exact equal_high_and_low_word_values_make_low31_replacement_exact _ _ producer.2

set_option pp.all true in
#check @a_high_word_at_least_two63_retains_that_lower_bound_after_low31_replacement
#print axioms a_high_word_at_least_two63_retains_that_lower_bound_after_low31_replacement
set_option pp.all true in
#check @a_full_input_below_the_scaled_low31_budget_has_a_small_initial_approximation
#print axioms a_full_input_below_the_scaled_low31_budget_has_a_small_initial_approximation
set_option pp.all true in
#check @original_nonzero_upper_window_derives_a_large_initial_approximation_sum
#print axioms original_nonzero_upper_window_derives_a_large_initial_approximation_sum
set_option pp.all true in
#check @equal_high_and_low_word_values_make_low31_replacement_exact
#print axioms equal_high_and_low_word_values_make_low31_replacement_exact
set_option pp.all true in
#check @original_zero_upper_window_returns_both_full_initial_approximations
#print axioms original_zero_upper_window_returns_both_full_initial_approximations
end ShielddSecurity.TransferBlstArmInverseInitialOperands01
