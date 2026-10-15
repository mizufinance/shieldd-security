import ShielddSecurity.TransferBlstArmInverseWindowBatchOdd01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseNaturalTermination01
open TransferBlstArmInverseBitlengthBudget01 (sourceNatBitlength)
open TransferBlstArmInverseFactors01 (SourceFactors sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)

/-! Symbolic exact natural-walk termination from pair bitlength. This covers
the exact final tail once the source batch schedule supplies its size bound.
The 512-step direct natural walk is a source-model result, not correspondence
to the native approximation schedule. GCD and native execution remain open. -/

theorem a_positive_natural_value_has_positive_exact_bitlength
    (value : Nat) (positive : 0 < value) : 1 ≤ sourceNatBitlength value := by
  simp only [sourceNatBitlength, if_neg (Nat.ne_of_gt positive)]
  omega

theorem an_odd_second_input_and_enough_exact_steps_force_a_zero_first_output
    (count : Nat) (s : SourceFactors) (odd : s.b % 2 = 1)
    (enough : sourceNatBitlength s.a + sourceNatBitlength s.b ≤ count) :
    (sourceFactorWalk count s).a = 0 := by
  have progress := TransferBlstArmInverseNaturalProgress01.every_original_natural_factor_walk_reaches_zero_or_decreases_by_its_length count s
  rcases progress with terminal | decreases
  · exact terminal
  · have finalOdd := TransferBlstArmInverseNaturalScale01.every_original_natural_factor_walk_retains_its_odd_second_input count s odd
    have positive : 0 < (sourceFactorWalk count s).b := by omega
    have bits := a_positive_natural_value_has_positive_exact_bitlength _ positive
    omega

theorem original_full_four_word_inputs_have_total_exact_bitlength_at_most512
    (a b : SourceFourWords) :
    sourceNatBitlength (sourcePackedFourWords a) + sourceNatBitlength (sourcePackedFourWords b) ≤ 512 := by
  have left := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power [a.w0, a.w1, a.w2, a.w3]
  have right := TransferScalarWordPrimitives01.packed_u64_vector_is_below_radix_power [b.w0, b.w1, b.w2, b.w3]
  have power : TransferScalarSerializationRange01.radix64 ^ 4 = (2 : Nat) ^ 256 := by
    simp only [TransferScalarSerializationRange01.radix64, ←Nat.pow_mul]
  change sourcePackedFourWords a < TransferScalarSerializationRange01.radix64 ^ 4 at left
  change sourcePackedFourWords b < TransferScalarSerializationRange01.radix64 ^ 4 at right
  rw [power] at left right
  have leftBits := TransferBlstArmInverseBitlengthBudget01.a_strict_upper_power_bounds_the_exact_natural_bitlength _ _ left
  have rightBits := TransferBlstArmInverseBitlengthBudget01.a_strict_upper_power_bounds_the_exact_natural_bitlength _ _ right
  omega

theorem original_full_four_word_exact_natural_walk_reaches_zero_by512
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    (sourceFactorWalk 512 (sourceFactorInitial (sourcePackedFourWords a) (sourcePackedFourWords b))).a = 0 := by
  exact an_odd_second_input_and_enough_exact_steps_force_a_zero_first_output _ _
    (TransferBlstArmInverseFirstMismatch01.original_odd_low_word_derives_odd_entire_four_word_input b oddB)
    (original_full_four_word_inputs_have_total_exact_bitlength_at_most512 a b)

theorem the_original_fifteen_batch_and_final47_step_budget_is_exactly512 :
    (15 : Nat) * 31 + 47 = 512 := by decide +kernel

set_option pp.all true in
#check @a_positive_natural_value_has_positive_exact_bitlength
#print axioms a_positive_natural_value_has_positive_exact_bitlength
set_option pp.all true in
#check @an_odd_second_input_and_enough_exact_steps_force_a_zero_first_output
#print axioms an_odd_second_input_and_enough_exact_steps_force_a_zero_first_output
set_option pp.all true in
#check @original_full_four_word_inputs_have_total_exact_bitlength_at_most512
#print axioms original_full_four_word_inputs_have_total_exact_bitlength_at_most512
set_option pp.all true in
#check @original_full_four_word_exact_natural_walk_reaches_zero_by512
#print axioms original_full_four_word_exact_natural_walk_reaches_zero_by512
set_option pp.all true in
#check @the_original_fifteen_batch_and_final47_step_budget_is_exactly512
#print axioms the_original_fifteen_batch_and_final47_step_budget_is_exactly512
end ShielddSecurity.TransferBlstArmInverseNaturalTermination01
