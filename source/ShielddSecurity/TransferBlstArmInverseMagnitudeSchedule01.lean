import ShielddSecurity.TransferBlstArmInversePairSchedule01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseMagnitudeSchedule01
open TransferBlstArmInverseMagnitudeBatch01 (sourceMagnitudeBatch)
open TransferBlstArmInversePairSchedule01 (PairStepContract symbolicPairSchedule)
open TransferBlstArmInverseBitlengthBudget01 (sourceNatBitlength)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)

/-! Concrete source-batch instantiation of the separately checked abstract
schedule. Every contract field is discharged by an original-window theorem.
The15+47 source schedule terminates; native operations and the inverse
coefficient/field correspondence remain separate obligations. -/

def originalSourceMagnitudeStepContract : PairStepContract sourceMagnitudeBatch :=
  ⟨TransferBlstArmInverseMagnitudeBatch01.every_source_magnitude_batch_with_odd_second_input_returns_an_odd_second_magnitude,
   TransferBlstArmInverseMagnitudeBatch01.every_source_magnitude_batch_with_odd_second_input_returns_two_values_that_fit_four_words,
   TransferBlstArmInverseMagnitudeBatch01.every_source_magnitude_batch_keeps_a_zero_first_input_zero,
   TransferBlstArmInverseMagnitudeBatch01.every_valid_source_magnitude_batch_reaches_zero_or_decreases_total_pair_bitlength_by31⟩

def sourceMagnitudeBatches (count : Nat) (input : Nat × Nat) : Nat × Nat :=
  symbolicPairSchedule sourceMagnitudeBatch count input

theorem every_symbolic_source_batch_schedule_keeps_its_second_input_odd
    (count : Nat) (input : Nat × Nat) (odd : input.2 % 2 = 1) :
    (sourceMagnitudeBatches count input).2 % 2 = 1 := by
  exact TransferBlstArmInversePairSchedule01.symbolic_schedule_retains_odd_second_value
    sourceMagnitudeBatch originalSourceMagnitudeStepContract count input odd

theorem every_valid_symbolic_source_batch_schedule_keeps_both_values_within_four_words
    (count : Nat) (input : Nat × Nat) (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256)
    (odd : input.2 % 2 = 1) :
    (sourceMagnitudeBatches count input).1 < 2 ^ 256 ∧ (sourceMagnitudeBatches count input).2 < 2 ^ 256 := by
  exact TransferBlstArmInversePairSchedule01.symbolic_schedule_retains_capacity
    sourceMagnitudeBatch originalSourceMagnitudeStepContract count input leftBound rightBound odd

theorem every_symbolic_source_batch_schedule_keeps_a_zero_first_input_zero
    (count : Nat) (input : Nat × Nat) (zero : input.1 = 0) :
    (sourceMagnitudeBatches count input).1 = 0 := by
  exact TransferBlstArmInversePairSchedule01.symbolic_schedule_retains_zero_first_value
    sourceMagnitudeBatch originalSourceMagnitudeStepContract count input zero

theorem every_valid_symbolic_source_batch_schedule_reaches_zero_or_decreases_size_by31_per_batch
    (count : Nat) (input : Nat × Nat) (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256)
    (odd : input.2 % 2 = 1) :
    (sourceMagnitudeBatches count input).1 = 0 ∨
      sourceNatBitlength (sourceMagnitudeBatches count input).1 +
        sourceNatBitlength (sourceMagnitudeBatches count input).2 + 31 * count ≤
          sourceNatBitlength input.1 + sourceNatBitlength input.2 := by
  exact TransferBlstArmInversePairSchedule01.symbolic_schedule_reaches_zero_or_decreases_size_by31_per_step
    sourceMagnitudeBatch originalSourceMagnitudeStepContract count input leftBound rightBound odd

theorem a_valid_source_batch_schedule_reaches_zero_or_leaves_only_its_exact_tail_size_budget
    (count remaining : Nat) (input : Nat × Nat)
    (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256) (odd : input.2 % 2 = 1)
    (budget : sourceNatBitlength input.1 + sourceNatBitlength input.2 ≤ 31 * count + remaining) :
    (sourceMagnitudeBatches count input).1 = 0 ∨
      sourceNatBitlength (sourceMagnitudeBatches count input).1 +
        sourceNatBitlength (sourceMagnitudeBatches count input).2 ≤ remaining := by
  exact TransferBlstArmInversePairSchedule01.symbolic_schedule_reaches_zero_or_leaves_the_tail_size_budget
    sourceMagnitudeBatch originalSourceMagnitudeStepContract count remaining input leftBound rightBound odd budget

theorem every_valid_source_batch_schedule_and_sufficient_exact_tail_reach_zero
    (count remaining : Nat) (input : Nat × Nat)
    (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256) (odd : input.2 % 2 = 1)
    (budget : sourceNatBitlength input.1 + sourceNatBitlength input.2 ≤ 31 * count + remaining) :
    (sourceFactorWalk remaining (sourceFactorInitial
      (sourceMagnitudeBatches count input).1 (sourceMagnitudeBatches count input).2)).a = 0 := by
  exact TransferBlstArmInversePairSchedule01.symbolic_schedule_and_a_sufficient_exact_natural_tail_reach_zero
    sourceMagnitudeBatch originalSourceMagnitudeStepContract count remaining input leftBound rightBound odd budget

theorem original_full_four_word_fifteen_batch_and_exact47_tail_source_schedule_reaches_zero
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    (sourceFactorWalk 47 (sourceFactorInitial
      (sourceMagnitudeBatches 15 (sourcePackedFourWords a, sourcePackedFourWords b)).1
      (sourceMagnitudeBatches 15 (sourcePackedFourWords a, sourcePackedFourWords b)).2)).a = 0 := by
  have initialSize := TransferBlstArmInverseNaturalTermination01.original_full_four_word_inputs_have_total_exact_bitlength_at_most512 a b
  have budget : sourceNatBitlength (sourcePackedFourWords a) + sourceNatBitlength (sourcePackedFourWords b) ≤ 31 * 15 + 47 := initialSize
  exact every_valid_source_batch_schedule_and_sufficient_exact_tail_reach_zero 15 47
    (sourcePackedFourWords a, sourcePackedFourWords b)
    (TransferBlstArmInverseBatchRange01.original_four_word_packing_is_strictly_below_two256 a)
    (TransferBlstArmInverseBatchRange01.original_four_word_packing_is_strictly_below_two256 b)
    (TransferBlstArmInverseFirstMismatch01.original_odd_low_word_derives_odd_entire_four_word_input b oddB) budget

set_option pp.all true in
#check @originalSourceMagnitudeStepContract
#print axioms originalSourceMagnitudeStepContract
set_option pp.all true in
#check @sourceMagnitudeBatches
#print axioms sourceMagnitudeBatches
set_option pp.all true in
#check @every_symbolic_source_batch_schedule_keeps_its_second_input_odd
#print axioms every_symbolic_source_batch_schedule_keeps_its_second_input_odd
set_option pp.all true in
#check @every_valid_symbolic_source_batch_schedule_keeps_both_values_within_four_words
#print axioms every_valid_symbolic_source_batch_schedule_keeps_both_values_within_four_words
set_option pp.all true in
#check @every_symbolic_source_batch_schedule_keeps_a_zero_first_input_zero
#print axioms every_symbolic_source_batch_schedule_keeps_a_zero_first_input_zero
set_option pp.all true in
#check @every_valid_symbolic_source_batch_schedule_reaches_zero_or_decreases_size_by31_per_batch
#print axioms every_valid_symbolic_source_batch_schedule_reaches_zero_or_decreases_size_by31_per_batch
set_option pp.all true in
#check @a_valid_source_batch_schedule_reaches_zero_or_leaves_only_its_exact_tail_size_budget
#print axioms a_valid_source_batch_schedule_reaches_zero_or_leaves_only_its_exact_tail_size_budget
set_option pp.all true in
#check @every_valid_source_batch_schedule_and_sufficient_exact_tail_reach_zero
#print axioms every_valid_source_batch_schedule_and_sufficient_exact_tail_reach_zero
set_option pp.all true in
#check @original_full_four_word_fifteen_batch_and_exact47_tail_source_schedule_reaches_zero
#print axioms original_full_four_word_fifteen_batch_and_exact47_tail_source_schedule_reaches_zero
end ShielddSecurity.TransferBlstArmInverseMagnitudeSchedule01
