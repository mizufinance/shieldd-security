import ShielddSecurity.TransferBlstArmInverseMagnitudeRows01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseTailCapacity01
open TransferBlstArmInverseBitlengthBudget01 (sourceNatBitlength)
open TransferBlstArmInverseMagnitudeSchedule01 (sourceMagnitudeBatches)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseWordRepack01 (sourceFourWordsOfNat)

/-! Source final-tail capacity, including early termination. Unit GCD forces
a stationary pair to be(0,1); otherwise the remaining pair-size budget bounds
both values. Thus original15-batch unit inputs fit47 bits and their modeled
low64 loads are exact. Actual stores/loads and native execution remain open. -/

theorem a_unit_pair_with_zero_or_a_positive_size_budget_fits_the_budget_power
    (left right width : Nat) (positive : 0 < width) (unit : Nat.gcd left right = 1)
    (cases : left = 0 ∨ sourceNatBitlength left + sourceNatBitlength right ≤ width) :
    left < 2 ^ width ∧ right < 2 ^ width := by
  rcases cases with terminal | small
  · rw [terminal, Nat.gcd_zero_left] at unit
    have powerLower : (2 : Nat) ^ 1 ≤ 2 ^ width := Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
    constructor <;> omega
  · have leftBits : sourceNatBitlength left ≤ width := by omega
    have rightBits : sourceNatBitlength right ≤ width := by omega
    exact ⟨Nat.lt_of_lt_of_le
      (TransferBlstArmInverseBitlengthBudget01.every_natural_value_is_strictly_below_its_exact_bitlength_power left)
      (Nat.pow_le_pow_right Nat.zero_lt_two leftBits),
      Nat.lt_of_lt_of_le
      (TransferBlstArmInverseBitlengthBudget01.every_natural_value_is_strictly_below_its_exact_bitlength_power right)
      (Nat.pow_le_pow_right Nat.zero_lt_two rightBits)⟩

theorem every_valid_unit_source_schedule_with_a_positive_tail_budget_returns_values_fitting_that_tail
    (count remaining : Nat) (input : Nat × Nat) (positive : 0 < remaining)
    (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256) (odd : input.2 % 2 = 1)
    (budget : sourceNatBitlength input.1 + sourceNatBitlength input.2 ≤ 31 * count + remaining)
    (unit : Nat.gcd input.1 input.2 = 1) :
    (sourceMagnitudeBatches count input).1 < 2 ^ remaining ∧ (sourceMagnitudeBatches count input).2 < 2 ^ remaining := by
  have preserved := TransferBlstArmInverseScheduleUnit01.every_valid_symbolic_magnitude_batch_schedule_preserves_the_entire_initial_gcd
    count input leftBound rightBound odd
  have cases := TransferBlstArmInverseMagnitudeSchedule01.a_valid_source_batch_schedule_reaches_zero_or_leaves_only_its_exact_tail_size_budget
    count remaining input leftBound rightBound odd budget
  exact a_unit_pair_with_zero_or_a_positive_size_budget_fits_the_budget_power _ _ remaining positive (preserved.trans unit) cases

theorem original_full_four_word_unit_inputs_leave_two_exact47_bit_values_after_fifteen_batches
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1)
    (unit : Nat.gcd (sourcePackedFourWords a) (sourcePackedFourWords b) = 1) :
    (sourceMagnitudeBatches 15 (sourcePackedFourWords a, sourcePackedFourWords b)).1 < 2 ^ 47 ∧
      (sourceMagnitudeBatches 15 (sourcePackedFourWords a, sourcePackedFourWords b)).2 < 2 ^ 47 := by
  have budget : sourceNatBitlength (sourcePackedFourWords a) + sourceNatBitlength (sourcePackedFourWords b) ≤ 31 * 15 + 47 :=
    TransferBlstArmInverseNaturalTermination01.original_full_four_word_inputs_have_total_exact_bitlength_at_most512 a b
  exact every_valid_unit_source_schedule_with_a_positive_tail_budget_returns_values_fitting_that_tail 15 47
    (sourcePackedFourWords a, sourcePackedFourWords b) (by decide)
    (TransferBlstArmInverseBatchRange01.original_four_word_packing_is_strictly_below_two256 a)
    (TransferBlstArmInverseBatchRange01.original_four_word_packing_is_strictly_below_two256 b)
    (TransferBlstArmInverseFirstMismatch01.original_odd_low_word_derives_odd_entire_four_word_input b oddB) budget unit

theorem every_repacked_value_below_two47_has_an_exact_low64_word
    (value : Nat) (bounded : value < 2 ^ 47) : (sourceFourWordsOfNat value).w0.toNat = value := by
  have power : (2 : Nat) ^ 47 ≤ 2 ^ 64 := by decide +kernel
  have entire : value < (2 : Nat) ^ 64 := Nat.lt_of_lt_of_le bounded power
  change (UInt64.ofNat value).toNat = value
  exact UInt64.toNat_ofNat_of_lt' entire

theorem original_fifteen_batch_unit_outputs_have_exact_modeled_low64_tail_loads
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1)
    (unit : Nat.gcd (sourcePackedFourWords a) (sourcePackedFourWords b) = 1) :
    let final := sourceMagnitudeBatches 15 (sourcePackedFourWords a, sourcePackedFourWords b)
    (sourceFourWordsOfNat final.1).w0.toNat = final.1 ∧ (sourceFourWordsOfNat final.2).w0.toNat = final.2 := by
  dsimp only
  have bounds := original_full_four_word_unit_inputs_leave_two_exact47_bit_values_after_fifteen_batches a b oddB unit
  exact ⟨every_repacked_value_below_two47_has_an_exact_low64_word _ bounds.1,
    every_repacked_value_below_two47_has_an_exact_low64_word _ bounds.2⟩

set_option pp.all true in
#check @a_unit_pair_with_zero_or_a_positive_size_budget_fits_the_budget_power
#print axioms a_unit_pair_with_zero_or_a_positive_size_budget_fits_the_budget_power
set_option pp.all true in
#check @every_valid_unit_source_schedule_with_a_positive_tail_budget_returns_values_fitting_that_tail
#print axioms every_valid_unit_source_schedule_with_a_positive_tail_budget_returns_values_fitting_that_tail
set_option pp.all true in
#check @original_full_four_word_unit_inputs_leave_two_exact47_bit_values_after_fifteen_batches
#print axioms original_full_four_word_unit_inputs_leave_two_exact47_bit_values_after_fifteen_batches
set_option pp.all true in
#check @every_repacked_value_below_two47_has_an_exact_low64_word
#print axioms every_repacked_value_below_two47_has_an_exact_low64_word
set_option pp.all true in
#check @original_fifteen_batch_unit_outputs_have_exact_modeled_low64_tail_loads
#print axioms original_fifteen_batch_unit_outputs_have_exact_modeled_low64_tail_loads
end ShielddSecurity.TransferBlstArmInverseTailCapacity01
