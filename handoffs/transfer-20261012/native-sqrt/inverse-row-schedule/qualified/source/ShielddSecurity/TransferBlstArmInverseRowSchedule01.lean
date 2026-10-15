import ShielddSecurity.TransferBlstArmInverseProducedRows01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseRowSchedule01
open TransferBlstArmInverseRowCompose01
  (SourceLinearRows SourceLinearTracks sourceIdentityRows sourceComposeRows)
open TransferBlstArmInversePairSchedule01 (PairStepContract symbolicPairSchedule)
open TransferBlstArmInverseMagnitudeBatch01 (sourceMagnitudeBatch)
open TransferBlstArmInverseMagnitudeSchedule01 (sourceMagnitudeBatches originalSourceMagnitudeStepContract)
open TransferBlstArmInverseProducedRows01 (sourcePrefixLinearRows)

/-! Symbolic accumulation of produced coefficient rows. The generic step
function is abstract throughout induction; the source instance supplies its
actual produced rows and every admitted-input property. Full exact scaling
is retained. Native extended coefficient storage remains separate. -/

def sourceAccumulateRows (step : Nat × Nat → Nat × Nat) (rows : Nat × Nat → SourceLinearRows) :
    Nat → Nat × Nat → SourceLinearRows → SourceLinearRows
  | 0, _, accumulated => accumulated
  | count + 1, input, accumulated =>
      sourceAccumulateRows step rows count (step input) (sourceComposeRows accumulated (rows input))

def sourceMagnitudeScheduleRows (count : Nat) (input : Nat × Nat) : SourceLinearRows :=
  sourceAccumulateRows sourceMagnitudeBatch (sourcePrefixLinearRows 31) count input sourceIdentityRows

theorem symbolic_accumulated_rows_track_the_entire_final_pair_at_the_product_scale
    (step : Nat × Nat → Nat × Nat) (rows : Nat × Nat → SourceLinearRows)
    (contract : PairStepContract step) (radix : Int)
    (produces : ∀ input, input.1 < 2 ^ 256 → input.2 < 2 ^ 256 → input.2 % 2 = 1 →
      SourceLinearTracks (input.1 : Int) (input.2 : Int) radix ((step input).1 : Int) ((step input).2 : Int) (rows input))
    (count : Nat) (input : Nat × Nat) (accumulated : SourceLinearRows) (scale inputA inputB : Int)
    (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256) (odd : input.2 % 2 = 1)
    (old : SourceLinearTracks inputA inputB scale (input.1 : Int) (input.2 : Int) accumulated) :
    SourceLinearTracks inputA inputB (scale * radix ^ count)
      ((symbolicPairSchedule step count input).1 : Int) ((symbolicPairSchedule step count input).2 : Int)
      (sourceAccumulateRows step rows count input accumulated) := by
  induction count generalizing input accumulated scale with
  | zero =>
    simpa only [sourceAccumulateRows, symbolicPairSchedule, Int.pow_zero, Int.mul_one] using old
  | succ count ih =>
    have nextBound := contract.capacity input odd
    have nextOdd := contract.odd input odd
    have nextTracked := TransferBlstArmInverseRowCompose01.two_exact_linear_row_steps_compose_at_the_product_of_their_scales
      inputA inputB (input.1 : Int) (input.2 : Int) ((step input).1 : Int) ((step input).2 : Int)
      scale radix accumulated (rows input) old (produces input leftBound rightBound odd)
    have previous := ih (input := step input) (accumulated := sourceComposeRows accumulated (rows input))
      (scale := scale * radix) nextBound.1 nextBound.2 nextOdd nextTracked
    have power : (scale * radix) * radix ^ count = scale * radix ^ (count + 1) := by
      rw [Int.pow_succ]
      ring1
    rw [power] at previous
    exact previous

theorem symbolic_produced_rows_initialized_at_identity_track_the_full_pair
    (step : Nat × Nat → Nat × Nat) (rows : Nat × Nat → SourceLinearRows)
    (contract : PairStepContract step) (radix : Int)
    (produces : ∀ input, input.1 < 2 ^ 256 → input.2 < 2 ^ 256 → input.2 % 2 = 1 →
      SourceLinearTracks (input.1 : Int) (input.2 : Int) radix ((step input).1 : Int) ((step input).2 : Int) (rows input))
    (count : Nat) (input : Nat × Nat) (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256)
    (odd : input.2 % 2 = 1) :
    SourceLinearTracks (input.1 : Int) (input.2 : Int) (radix ^ count)
      ((symbolicPairSchedule step count input).1 : Int) ((symbolicPairSchedule step count input).2 : Int)
      (sourceAccumulateRows step rows count input sourceIdentityRows) := by
  have tracked := symbolic_accumulated_rows_track_the_entire_final_pair_at_the_product_scale
    step rows contract radix produces count input sourceIdentityRows 1 (input.1 : Int) (input.2 : Int)
    leftBound rightBound odd
    (TransferBlstArmInverseRowCompose01.the_identity_rows_track_both_original_inputs_at_scale_one _ _)
  simpa only [Int.one_mul] using tracked

theorem original_source_magnitude_schedule_rows_track_both_full_outputs_at_the_exact_radix_power
    (count : Nat) (input : Nat × Nat) (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256)
    (odd : input.2 % 2 = 1) :
    SourceLinearTracks (input.1 : Int) (input.2 : Int) ((2 : Int) ^ (31 * count))
      ((sourceMagnitudeBatches count input).1 : Int) ((sourceMagnitudeBatches count input).2 : Int)
      (sourceMagnitudeScheduleRows count input) := by
  have tracked := symbolic_produced_rows_initialized_at_identity_track_the_full_pair
    sourceMagnitudeBatch (sourcePrefixLinearRows 31) originalSourceMagnitudeStepContract ((2 : Int) ^ 31)
    TransferBlstArmInverseProducedRows01.original_magnitude_batch_produces_its_exact_full_sign_corrected_rows
    count input leftBound rightBound odd
  have power : ((2 : Int) ^ 31) ^ count = (2 : Int) ^ (31 * count) := Int.pow_mul.symm
  rw [power] at tracked
  exact tracked

set_option pp.all true in
#check @sourceAccumulateRows
#print axioms sourceAccumulateRows
set_option pp.all true in
#check @sourceMagnitudeScheduleRows
#print axioms sourceMagnitudeScheduleRows
set_option pp.all true in
#check @symbolic_accumulated_rows_track_the_entire_final_pair_at_the_product_scale
#print axioms symbolic_accumulated_rows_track_the_entire_final_pair_at_the_product_scale
set_option pp.all true in
#check @symbolic_produced_rows_initialized_at_identity_track_the_full_pair
#print axioms symbolic_produced_rows_initialized_at_identity_track_the_full_pair
set_option pp.all true in
#check @original_source_magnitude_schedule_rows_track_both_full_outputs_at_the_exact_radix_power
#print axioms original_source_magnitude_schedule_rows_track_both_full_outputs_at_the_exact_radix_power
end ShielddSecurity.TransferBlstArmInverseRowSchedule01
