import ShielddSecurity.TransferBlstArmInverseRowSchedule01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseFullRows01
open TransferBlstArmInverseRowCompose01 (SourceLinearRows SourceLinearTracks sourceComposeRows)
open TransferBlstArmInverseFactors01 (sourceFactorInitial sourceFactorWalk)
open TransferBlstArmInverseMagnitudeSchedule01 (sourceMagnitudeBatches)
open TransferBlstArmInverseRowSchedule01 (sourceMagnitudeScheduleRows)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)

/-! Exact full coefficient rows after source magnitude batches and the exact
natural tail. The scale is retained symbolically, then specialized to2^512.
No row or quotient observation is supplied. Native extended coefficients,
reduction and compiled correspondence remain separate. -/

def sourceExactTailPair (count : Nat) (input : Nat × Nat) : Nat × Nat :=
  let factors := sourceFactorWalk count (sourceFactorInitial input.1 input.2)
  (factors.a, factors.b)

def sourceExactTailLinearRows (count : Nat) (input : Nat × Nat) : SourceLinearRows :=
  let factors := sourceFactorWalk count (sourceFactorInitial input.1 input.2)
  ⟨factors.f0, factors.g0, factors.f1, factors.g1⟩

def sourceFinalLinearRows (count remaining : Nat) (input : Nat × Nat) : SourceLinearRows :=
  sourceComposeRows (sourceMagnitudeScheduleRows count input)
    (sourceExactTailLinearRows remaining (sourceMagnitudeBatches count input))

theorem the_initialized_exact_natural_tail_produces_both_full_scaled_input_rows
    (count : Nat) (input : Nat × Nat) (odd : input.2 % 2 = 1) :
    SourceLinearTracks (input.1 : Int) (input.2 : Int) ((2 : Int) ^ count)
      ((sourceExactTailPair count input).1 : Int) ((sourceExactTailPair count input).2 : Int)
      (sourceExactTailLinearRows count input) := by
  have tracked := TransferBlstArmInverseFactors01.original_initialized_factor_walk_derives_exact_scaled_input_rows
    count input.1 input.2 odd
  exact tracked

theorem original_magnitude_batches_and_exact_tail_rows_track_both_entire_inputs_at_the_exact_scale
    (count remaining : Nat) (input : Nat × Nat) (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256)
    (odd : input.2 % 2 = 1) :
    SourceLinearTracks (input.1 : Int) (input.2 : Int) ((2 : Int) ^ (31 * count + remaining))
      ((sourceExactTailPair remaining (sourceMagnitudeBatches count input)).1 : Int)
      ((sourceExactTailPair remaining (sourceMagnitudeBatches count input)).2 : Int)
      (sourceFinalLinearRows count remaining input) := by
  have previous := TransferBlstArmInverseRowSchedule01.original_source_magnitude_schedule_rows_track_both_full_outputs_at_the_exact_radix_power
    count input leftBound rightBound odd
  have intermediateOdd := TransferBlstArmInverseMagnitudeSchedule01.every_symbolic_source_batch_schedule_keeps_its_second_input_odd count input odd
  have tail := the_initialized_exact_natural_tail_produces_both_full_scaled_input_rows remaining (sourceMagnitudeBatches count input) intermediateOdd
  have composed := TransferBlstArmInverseRowCompose01.two_exact_linear_row_steps_compose_at_the_product_of_their_scales
    (input.1 : Int) (input.2 : Int)
    ((sourceMagnitudeBatches count input).1 : Int) ((sourceMagnitudeBatches count input).2 : Int)
    ((sourceExactTailPair remaining (sourceMagnitudeBatches count input)).1 : Int)
    ((sourceExactTailPair remaining (sourceMagnitudeBatches count input)).2 : Int)
    ((2 : Int) ^ (31 * count)) ((2 : Int) ^ remaining)
    (sourceMagnitudeScheduleRows count input) (sourceExactTailLinearRows remaining (sourceMagnitudeBatches count input)) previous tail
  have power : (2 : Int) ^ (31 * count) * (2 : Int) ^ remaining = (2 : Int) ^ (31 * count + remaining) :=
    (Int.pow_add 2 (31 * count) remaining).symm
  rw [power] at composed
  exact composed

theorem original_full_four_word_fifteen_batch_and_exact47_tail_rows_have_exact_scale_two512
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1) :
    SourceLinearTracks (sourcePackedFourWords a : Int) (sourcePackedFourWords b : Int) ((2 : Int) ^ 512)
      ((sourceExactTailPair 47 (sourceMagnitudeBatches 15 (sourcePackedFourWords a, sourcePackedFourWords b))).1 : Int)
      ((sourceExactTailPair 47 (sourceMagnitudeBatches 15 (sourcePackedFourWords a, sourcePackedFourWords b))).2 : Int)
      (sourceFinalLinearRows 15 47 (sourcePackedFourWords a, sourcePackedFourWords b)) := by
  exact original_magnitude_batches_and_exact_tail_rows_track_both_entire_inputs_at_the_exact_scale 15 47
    (sourcePackedFourWords a, sourcePackedFourWords b)
    (TransferBlstArmInverseBatchRange01.original_four_word_packing_is_strictly_below_two256 a)
    (TransferBlstArmInverseBatchRange01.original_four_word_packing_is_strictly_below_two256 b)
    (TransferBlstArmInverseFirstMismatch01.original_odd_low_word_derives_odd_entire_four_word_input b oddB)

set_option pp.all true in
#check @sourceExactTailPair
#print axioms sourceExactTailPair
set_option pp.all true in
#check @sourceExactTailLinearRows
#print axioms sourceExactTailLinearRows
set_option pp.all true in
#check @sourceFinalLinearRows
#print axioms sourceFinalLinearRows
set_option pp.all true in
#check @the_initialized_exact_natural_tail_produces_both_full_scaled_input_rows
#print axioms the_initialized_exact_natural_tail_produces_both_full_scaled_input_rows
set_option pp.all true in
#check @original_magnitude_batches_and_exact_tail_rows_track_both_entire_inputs_at_the_exact_scale
#print axioms original_magnitude_batches_and_exact_tail_rows_track_both_entire_inputs_at_the_exact_scale
set_option pp.all true in
#check @original_full_four_word_fifteen_batch_and_exact47_tail_rows_have_exact_scale_two512
#print axioms original_full_four_word_fifteen_batch_and_exact47_tail_rows_have_exact_scale_two512
end ShielddSecurity.TransferBlstArmInverseFullRows01
