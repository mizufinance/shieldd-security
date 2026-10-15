import ShielddSecurity.TransferBlstArmInverseNaturalGcd01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseScheduleUnit01
open TransferBlstArmInverseMagnitudeBatch01 (sourceMagnitudeBatch)
open TransferBlstArmInverseMagnitudeSchedule01 (sourceMagnitudeBatches)
open TransferBlstArmInverseBitlengthBudget01 (sourceNatBitlength)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInversePairSchedule01 (PairStepContract symbolicPairSchedule)
attribute [local irreducible] sourceMagnitudeBatch

/-! Full source schedule unit output. Exact magnitude batches preserve the
initial GCD; symbolic termination and the exact natural tail then give the
pair(0,1) under explicit unit initial GCD. Prime/canonical runtime origins,
inverse coefficient invariant and native execution remain separate. -/

theorem an_abstract_valid_pair_schedule_with_gcd_preserving_steps_preserves_the_initial_gcd
    (step : Nat × Nat → Nat × Nat) (contract : PairStepContract step)
    (keepsGcd : ∀ input, input.1 < 2 ^ 256 → input.2 < 2 ^ 256 → input.2 % 2 = 1 →
      Nat.gcd (step input).1 (step input).2 = Nat.gcd input.1 input.2)
    (count : Nat) (input : Nat × Nat) (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256)
    (odd : input.2 % 2 = 1) :
    Nat.gcd (symbolicPairSchedule step count input).1 (symbolicPairSchedule step count input).2 = Nat.gcd input.1 input.2 := by
  induction count generalizing input with
  | zero => rfl
  | succ count ih =>
    have nextBound := contract.capacity input odd
    have previous := ih (step input) nextBound.1 nextBound.2 (contract.odd input odd)
    have first := keepsGcd input leftBound rightBound odd
    exact previous.trans first

theorem every_valid_symbolic_magnitude_batch_schedule_preserves_the_entire_initial_gcd
    (count : Nat) (input : Nat × Nat) (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256)
    (odd : input.2 % 2 = 1) :
    Nat.gcd (sourceMagnitudeBatches count input).1 (sourceMagnitudeBatches count input).2 = Nat.gcd input.1 input.2 := by
  exact an_abstract_valid_pair_schedule_with_gcd_preserving_steps_preserves_the_initial_gcd
    sourceMagnitudeBatch TransferBlstArmInverseMagnitudeSchedule01.originalSourceMagnitudeStepContract
    TransferBlstArmInverseWindowGcd01.every_valid_source_magnitude_batch_preserves_the_entire_input_gcd
    count input leftBound rightBound odd

theorem every_sufficient_valid_source_schedule_with_unit_initial_gcd_finishes_at_zero_one
    (count remaining : Nat) (input : Nat × Nat)
    (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256) (odd : input.2 % 2 = 1)
    (budget : sourceNatBitlength input.1 + sourceNatBitlength input.2 ≤ 31 * count + remaining)
    (unit : Nat.gcd input.1 input.2 = 1) :
    let final := sourceFactorWalk remaining (sourceFactorInitial
      (sourceMagnitudeBatches count input).1 (sourceMagnitudeBatches count input).2)
    final.a = 0 ∧ final.b = 1 := by
  dsimp only
  have terminal := TransferBlstArmInverseMagnitudeSchedule01.every_valid_source_batch_schedule_and_sufficient_exact_tail_reach_zero
    count remaining input leftBound rightBound odd budget
  have preserved := every_valid_symbolic_magnitude_batch_schedule_preserves_the_entire_initial_gcd count input leftBound rightBound odd
  have finalUnit : Nat.gcd (sourceMagnitudeBatches count input).1 (sourceMagnitudeBatches count input).2 = 1 := preserved.trans unit
  have finalOdd := TransferBlstArmInverseMagnitudeSchedule01.every_symbolic_source_batch_schedule_keeps_its_second_input_odd count input odd
  have second := TransferBlstArmInverseNaturalGcd01.an_exact_natural_tail_with_unit_initial_gcd_and_zero_first_output_has_second_output_one
    remaining (sourceFactorInitial (sourceMagnitudeBatches count input).1 (sourceMagnitudeBatches count input).2) finalOdd finalUnit terminal
  exact ⟨terminal, second⟩

theorem original_full_four_word_unit_inputs_finish_the_fifteen_batch_and_exact47_tail_at_zero_one
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1)
    (unit : Nat.gcd (sourcePackedFourWords a) (sourcePackedFourWords b) = 1) :
    let final := sourceFactorWalk 47 (sourceFactorInitial
      (sourceMagnitudeBatches 15 (sourcePackedFourWords a, sourcePackedFourWords b)).1
      (sourceMagnitudeBatches 15 (sourcePackedFourWords a, sourcePackedFourWords b)).2)
    final.a = 0 ∧ final.b = 1 := by
  have initialSize := TransferBlstArmInverseNaturalTermination01.original_full_four_word_inputs_have_total_exact_bitlength_at_most512 a b
  have budget : sourceNatBitlength (sourcePackedFourWords a) + sourceNatBitlength (sourcePackedFourWords b) ≤ 31 * 15 + 47 := initialSize
  exact every_sufficient_valid_source_schedule_with_unit_initial_gcd_finishes_at_zero_one 15 47
    (sourcePackedFourWords a, sourcePackedFourWords b)
    (TransferBlstArmInverseBatchRange01.original_four_word_packing_is_strictly_below_two256 a)
    (TransferBlstArmInverseBatchRange01.original_four_word_packing_is_strictly_below_two256 b)
    (TransferBlstArmInverseFirstMismatch01.original_odd_low_word_derives_odd_entire_four_word_input b oddB) budget unit

set_option pp.all true in
#check @an_abstract_valid_pair_schedule_with_gcd_preserving_steps_preserves_the_initial_gcd
#print axioms an_abstract_valid_pair_schedule_with_gcd_preserving_steps_preserves_the_initial_gcd
set_option pp.all true in
#check @every_valid_symbolic_magnitude_batch_schedule_preserves_the_entire_initial_gcd
#print axioms every_valid_symbolic_magnitude_batch_schedule_preserves_the_entire_initial_gcd
set_option pp.all true in
#check @every_sufficient_valid_source_schedule_with_unit_initial_gcd_finishes_at_zero_one
#print axioms every_sufficient_valid_source_schedule_with_unit_initial_gcd_finishes_at_zero_one
set_option pp.all true in
#check @original_full_four_word_unit_inputs_finish_the_fifteen_batch_and_exact47_tail_at_zero_one
#print axioms original_full_four_word_unit_inputs_finish_the_fifteen_batch_and_exact47_tail_at_zero_one
end ShielddSecurity.TransferBlstArmInverseScheduleUnit01
