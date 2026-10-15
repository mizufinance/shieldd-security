import ShielddSecurity.TransferBlstArmInverseFullRows01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseScaledInverse01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseMagnitudeSchedule01 (sourceMagnitudeBatches)
open TransferBlstArmInverseFullRows01 (sourceFinalLinearRows sourceExactTailPair)
open TransferBlstArmInverseBitlengthBudget01 (sourceNatBitlength)

/-! Scaled source inverse from the produced full coefficient matrix and
proved unit endpoint. The coefficient is computed by original batches and
the exact tail, not supplied. Runtime unit/canonical origins, native stored
coefficient/sign handling and Montgomery reduction remain open. -/

def sourceScaledInverseCoefficient (a b : SourceFourWords) : Int :=
  (sourceFinalLinearRows 15 47 (sourcePackedFourWords a, sourcePackedFourWords b)).f1

def sourceScaledModulusCoefficient (a b : SourceFourWords) : Int :=
  (sourceFinalLinearRows 15 47 (sourcePackedFourWords a, sourcePackedFourWords b)).g1

theorem an_exact_integer_bezout_row_derives_the_scaled_inverse_residue
    (input modulus coefficient other scale : Int)
    (row : coefficient * input + other * modulus = scale) :
    (coefficient * input) % modulus = scale % modulus := by
  have reduced := congrArg (fun value : Int => value % modulus) row
  dsimp only at reduced
  rw [Int.add_mul_emod_self_right] at reduced
  exact reduced

theorem every_sufficient_valid_unit_source_schedule_produces_the_exact_scaled_bezout_identity
    (count remaining : Nat) (input : Nat × Nat)
    (leftBound : input.1 < 2 ^ 256) (rightBound : input.2 < 2 ^ 256) (odd : input.2 % 2 = 1)
    (budget : sourceNatBitlength input.1 + sourceNatBitlength input.2 ≤ 31 * count + remaining)
    (unit : Nat.gcd input.1 input.2 = 1) :
    (sourceFinalLinearRows count remaining input).f1 * (input.1 : Int) +
      (sourceFinalLinearRows count remaining input).g1 * (input.2 : Int) = (2 : Int) ^ (31 * count + remaining) := by
  have tracked := TransferBlstArmInverseFullRows01.original_magnitude_batches_and_exact_tail_rows_track_both_entire_inputs_at_the_exact_scale
    count remaining input leftBound rightBound odd
  have terminal := TransferBlstArmInverseScheduleUnit01.every_sufficient_valid_source_schedule_with_unit_initial_gcd_finishes_at_zero_one
    count remaining input leftBound rightBound odd budget unit
  have secondOne : (sourceExactTailPair remaining (sourceMagnitudeBatches count input)).2 = 1 := terminal.2
  have last := tracked.2
  rw [secondOne, Nat.cast_one, Int.mul_one] at last
  exact last.symm

theorem original_four_word_unit_inputs_produce_the_exact_two512_bezout_identity
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1)
    (unit : Nat.gcd (sourcePackedFourWords a) (sourcePackedFourWords b) = 1) :
    sourceScaledInverseCoefficient a b * (sourcePackedFourWords a : Int) +
      sourceScaledModulusCoefficient a b * (sourcePackedFourWords b : Int) = (2 : Int) ^ 512 := by
  have budget : sourceNatBitlength (sourcePackedFourWords a) + sourceNatBitlength (sourcePackedFourWords b) ≤ 31 * 15 + 47 :=
    TransferBlstArmInverseNaturalTermination01.original_full_four_word_inputs_have_total_exact_bitlength_at_most512 a b
  exact every_sufficient_valid_unit_source_schedule_produces_the_exact_scaled_bezout_identity 15 47
    (sourcePackedFourWords a, sourcePackedFourWords b)
    (TransferBlstArmInverseBatchRange01.original_four_word_packing_is_strictly_below_two256 a)
    (TransferBlstArmInverseBatchRange01.original_four_word_packing_is_strictly_below_two256 b)
    (TransferBlstArmInverseFirstMismatch01.original_odd_low_word_derives_odd_entire_four_word_input b oddB) budget unit

theorem original_four_word_unit_inputs_produce_the_actual_source_scaled_inverse_residue
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1)
    (unit : Nat.gcd (sourcePackedFourWords a) (sourcePackedFourWords b) = 1) :
    (sourceScaledInverseCoefficient a b * (sourcePackedFourWords a : Int)) % (sourcePackedFourWords b : Int) =
      (2 : Int) ^ 512 % (sourcePackedFourWords b : Int) := by
  exact an_exact_integer_bezout_row_derives_the_scaled_inverse_residue _ _ _ _ _
    (original_four_word_unit_inputs_produce_the_exact_two512_bezout_identity a b oddB unit)

set_option pp.all true in
#check @sourceScaledInverseCoefficient
#print axioms sourceScaledInverseCoefficient
set_option pp.all true in
#check @sourceScaledModulusCoefficient
#print axioms sourceScaledModulusCoefficient
set_option pp.all true in
#check @an_exact_integer_bezout_row_derives_the_scaled_inverse_residue
#print axioms an_exact_integer_bezout_row_derives_the_scaled_inverse_residue
set_option pp.all true in
#check @every_sufficient_valid_unit_source_schedule_produces_the_exact_scaled_bezout_identity
#print axioms every_sufficient_valid_unit_source_schedule_produces_the_exact_scaled_bezout_identity
set_option pp.all true in
#check @original_four_word_unit_inputs_produce_the_exact_two512_bezout_identity
#print axioms original_four_word_unit_inputs_produce_the_exact_two512_bezout_identity
set_option pp.all true in
#check @original_four_word_unit_inputs_produce_the_actual_source_scaled_inverse_residue
#print axioms original_four_word_unit_inputs_produce_the_actual_source_scaled_inverse_residue
end ShielddSecurity.TransferBlstArmInverseScaledInverse01
