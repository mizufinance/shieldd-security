import ShielddSecurity.TransferBlstArmInverseRowNorm01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseCoefficientBounds01
open TransferBlstArmInverseRowNorm01 (SourceLinearRowsBound)
open TransferBlstArmInverseRowCompose01 (SourceLinearRows sourceComposeRows sourceIdentityRows)
open TransferBlstArmInverseRowSchedule01 (sourceAccumulateRows sourceMagnitudeScheduleRows)
open TransferBlstArmInverseProducedRows01 (sourcePrefixLinearRows)
open TransferBlstArmInverseMagnitudeBatch01 (sourceMagnitudeBatch)
open TransferBlstArmInverseMagnitudeSchedule01 (sourceMagnitudeBatches)
open TransferBlstArmInverseFullRows01 (sourceExactTailLinearRows sourceFinalLinearRows)
open TransferBlstArmInverseScaledInverse01 (sourceScaledInverseCoefficient sourceScaledModulusCoefficient)
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)

/-! Produced coefficient bounds from symbolic row sums, with no selected
matrix bound premise at the source endpoints. Sign-corrected prefixes,
accumulated batches and exact tails give final coefficient magnitudes at
most2^512. This bound includes the endpoint and does not itself prove a
native finite-width encoding or carry/sign interpretation. -/

theorem every_original_sign_corrected_prefix_row_sum_is_at_most_its_radix_power
    (count : Nat) (input : Nat × Nat) : SourceLinearRowsBound (2 ^ count) (sourcePrefixLinearRows count input) := by
  let a := TransferBlstArmInverseWordRepack01.sourceFourWordsOfNat input.1
  let b := TransferBlstArmInverseWordRepack01.sourceFourWordsOfNat input.2
  let approxA := TransferBlstArmInverseApproxBits01.sourceApproxLow31
    (TransferBlstArmInverseWindowInput01.sourceFourWordWindowWords a b).1 a.w0
  let approxB := TransferBlstArmInverseApproxBits01.sourceApproxLow31
    (TransferBlstArmInverseWindowInput01.sourceFourWordWindowWords a b).2 b.w0
  have original := TransferBlstArmInverseNorm01.original_initialized_factor_walk_derives_row_sums_at_most_its_radix_power count approxA approxB
  dsimp only [SourceLinearRowsBound, sourcePrefixLinearRows]
  rw [TransferBlstArmInverseRowNorm01.simultaneous_source_row_sign_correction_preserves_its_entire_row_sum,
    TransferBlstArmInverseRowNorm01.simultaneous_source_row_sign_correction_preserves_its_entire_row_sum]
  exact original

theorem symbolic_coefficient_accumulation_multiplies_the_bound_by_the_step_power
    (step : Nat × Nat → Nat × Nat) (rows : Nat × Nat → SourceLinearRows)
    (bound : Nat) (produces : ∀ input, SourceLinearRowsBound bound (rows input))
    (count : Nat) (input : Nat × Nat) (accumulated : SourceLinearRows) (oldBound : Nat)
    (old : SourceLinearRowsBound oldBound accumulated) :
    SourceLinearRowsBound (bound ^ count * oldBound) (sourceAccumulateRows step rows count input accumulated) := by
  induction count generalizing input accumulated oldBound with
  | zero => simpa only [sourceAccumulateRows, Nat.pow_zero, Nat.one_mul] using old
  | succ count ih =>
    have next := TransferBlstArmInverseRowNorm01.exact_coefficient_row_composition_derives_the_product_of_both_row_sum_bounds
      accumulated (rows input) oldBound bound old (produces input)
    have previous := ih (input := step input) (accumulated := sourceComposeRows accumulated (rows input))
      (oldBound := oldBound * bound) next
    have power : bound ^ count * (oldBound * bound) = bound ^ (count + 1) * oldBound := by
      rw [Nat.pow_succ]
      ring1
    rw [power] at previous
    exact previous

theorem every_original_magnitude_schedule_row_sum_is_at_most_its_exact_radix_power
    (count : Nat) (input : Nat × Nat) :
    SourceLinearRowsBound (2 ^ (31 * count)) (sourceMagnitudeScheduleRows count input) := by
  have accumulated := symbolic_coefficient_accumulation_multiplies_the_bound_by_the_step_power
    sourceMagnitudeBatch (sourcePrefixLinearRows 31) (2 ^ 31)
    (every_original_sign_corrected_prefix_row_sum_is_at_most_its_radix_power 31)
    count input sourceIdentityRows 1 TransferBlstArmInverseRowNorm01.original_identity_coefficient_rows_have_both_row_sums_at_most_one
  have power : ((2 : Nat) ^ 31) ^ count = 2 ^ (31 * count) := (Nat.pow_mul 2 31 count).symm
  rw [Nat.mul_one, power] at accumulated
  exact accumulated

theorem every_original_exact_tail_row_sum_is_at_most_its_radix_power
    (count : Nat) (input : Nat × Nat) :
    SourceLinearRowsBound (2 ^ count) (sourceExactTailLinearRows count input) := by
  exact TransferBlstArmInverseNorm01.original_initialized_factor_walk_derives_row_sums_at_most_its_radix_power count input.1 input.2

theorem every_original_full_source_schedule_row_sum_is_at_most_its_total_radix_power
    (count remaining : Nat) (input : Nat × Nat) :
    SourceLinearRowsBound (2 ^ (31 * count + remaining)) (sourceFinalLinearRows count remaining input) := by
  have previous := every_original_magnitude_schedule_row_sum_is_at_most_its_exact_radix_power count input
  have tail := every_original_exact_tail_row_sum_is_at_most_its_radix_power remaining (sourceMagnitudeBatches count input)
  have composed := TransferBlstArmInverseRowNorm01.exact_coefficient_row_composition_derives_the_product_of_both_row_sum_bounds
    (sourceMagnitudeScheduleRows count input) (sourceExactTailLinearRows remaining (sourceMagnitudeBatches count input))
    (2 ^ (31 * count)) (2 ^ remaining) previous tail
  rw [←Nat.pow_add] at composed
  exact composed

theorem both_original_final_row_coefficients_have_magnitude_at_most_the_total_radix_power
    (count remaining : Nat) (input : Nat × Nat) :
    (sourceFinalLinearRows count remaining input).f1.natAbs ≤ 2 ^ (31 * count + remaining) ∧
      (sourceFinalLinearRows count remaining input).g1.natAbs ≤ 2 ^ (31 * count + remaining) := by
  have bounded := every_original_full_source_schedule_row_sum_is_at_most_its_total_radix_power count remaining input
  exact ⟨Nat.le_trans (Nat.le_add_right _ _) bounded.2, Nat.le_trans (Nat.le_add_left _ _) bounded.2⟩

-- Permit the concrete 65-byte endpoint power during definitional comparison.
set_option exponentiation.threshold 512 in
theorem both_produced_original_source_inverse_coefficients_have_magnitude_at_most_two512
    (a b : SourceFourWords) :
    (sourceScaledInverseCoefficient a b).natAbs ≤ 2 ^ 512 ∧
      (sourceScaledModulusCoefficient a b).natAbs ≤ 2 ^ 512 := by
  exact both_original_final_row_coefficients_have_magnitude_at_most_the_total_radix_power
    15 47 (sourcePackedFourWords a, sourcePackedFourWords b)

set_option pp.all true in
#check @every_original_sign_corrected_prefix_row_sum_is_at_most_its_radix_power
#print axioms every_original_sign_corrected_prefix_row_sum_is_at_most_its_radix_power
set_option pp.all true in
#check @symbolic_coefficient_accumulation_multiplies_the_bound_by_the_step_power
#print axioms symbolic_coefficient_accumulation_multiplies_the_bound_by_the_step_power
set_option pp.all true in
#check @every_original_magnitude_schedule_row_sum_is_at_most_its_exact_radix_power
#print axioms every_original_magnitude_schedule_row_sum_is_at_most_its_exact_radix_power
set_option pp.all true in
#check @every_original_exact_tail_row_sum_is_at_most_its_radix_power
#print axioms every_original_exact_tail_row_sum_is_at_most_its_radix_power
set_option pp.all true in
#check @every_original_full_source_schedule_row_sum_is_at_most_its_total_radix_power
#print axioms every_original_full_source_schedule_row_sum_is_at_most_its_total_radix_power
set_option pp.all true in
#check @both_original_final_row_coefficients_have_magnitude_at_most_the_total_radix_power
#print axioms both_original_final_row_coefficients_have_magnitude_at_most_the_total_radix_power
set_option pp.all true in
#check @both_produced_original_source_inverse_coefficients_have_magnitude_at_most_two512
#print axioms both_produced_original_source_inverse_coefficients_have_magnitude_at_most_two512
end ShielddSecurity.TransferBlstArmInverseCoefficientBounds01
