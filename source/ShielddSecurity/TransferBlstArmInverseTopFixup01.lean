import ShielddSecurity.TransferBlstArmInverseCoefficientBounds01
import ShielddSecurity.TransferBlstArmInverseSign01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseTopFixup01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseScaledInverse01 (sourceScaledInverseCoefficient)
open TransferBlstArmInverseSign01 (sourceWideRadix sourceCorrectionShift sourceSignedCorrection)
open TransferBoundedNativeCodec01 (nullifierModulus)

/-! Connect the derived coefficient to the existing original rx2 adjustment
model. No selected coefficient bound is supplied. Actual native top/carry,
mask/add/store and Montgomery execution correspondence remains separate. -/

set_option exponentiation.threshold 512 in
theorem original_unsigned_wide_radix_is_exactly_two512 :
    sourceWideRadix = ((2 ^ 512 : Nat) : Int) := by decide

set_option exponentiation.threshold 512 in
theorem every_original_produced_inverse_coefficient_satisfies_both_signed_wide_bounds
    (a b : SourceFourWords) :
    -sourceWideRadix ≤ sourceScaledInverseCoefficient a b ∧
      sourceScaledInverseCoefficient a b ≤ sourceWideRadix := by
  have bound := (TransferBlstArmInverseCoefficientBounds01.both_produced_original_source_inverse_coefficients_have_magnitude_at_most_two512 a b).1
  have castBound : ((sourceScaledInverseCoefficient a b).natAbs : Int) ≤ ((2 ^ 512 : Nat) : Int) :=
    Int.ofNat_le.mpr bound
  rw [←original_unsigned_wide_radix_is_exactly_two512] at castBound
  have upper := Int.le_natAbs (a := sourceScaledInverseCoefficient a b)
  have lower := Int.le_natAbs (a := -sourceScaledInverseCoefficient a b)
  rw [Int.natAbs_neg] at lower
  constructor <;> omega

def sourceNormalizedInverseCoefficient (a b : SourceFourWords) : Int :=
  sourceSignedCorrection (sourceScaledInverseCoefficient a b)

theorem every_original_produced_inverse_coefficient_normalizes_to_the_full_unsigned_wide_range
    (a b : SourceFourWords) :
    0 ≤ sourceNormalizedInverseCoefficient a b ∧ sourceNormalizedInverseCoefficient a b < sourceWideRadix := by
  have bounded := every_original_produced_inverse_coefficient_satisfies_both_signed_wide_bounds a b
  exact TransferBlstArmInverseSign01.original_two_signed_adjustments_derive_unsigned_wide_range _ bounded.1 bounded.2

theorem original_rx2_correction_shift_has_zero_entire_integer_scalar_modulus_residue :
    sourceCorrectionShift % (nullifierModulus : Int) = 0 := by decide

theorem original_rx2_signed_adjustments_preserve_the_entire_integer_scalar_modulus_residue
    (value : Int) : sourceSignedCorrection value % (nullifierModulus : Int) = value % (nullifierModulus : Int) := by
  have multiple := original_rx2_correction_shift_has_zero_entire_integer_scalar_modulus_residue
  dsimp only [sourceSignedCorrection, TransferBlstArmInverseSign01.sourceSignedFirst]
  split_ifs <;> simp only [Int.add_emod, Int.sub_emod, multiple, Int.add_zero, Int.sub_zero, Int.emod_emod]

theorem original_unit_scalar_inputs_produce_a_normalized_scaled_inverse_residue
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1)
    (modulus : sourcePackedFourWords b = nullifierModulus)
    (unit : Nat.gcd (sourcePackedFourWords a) (sourcePackedFourWords b) = 1) :
    (sourceNormalizedInverseCoefficient a b * (sourcePackedFourWords a : Int)) % (nullifierModulus : Int) =
      (2 : Int) ^ 512 % (nullifierModulus : Int) := by
  have inverse := TransferBlstArmInverseScaledInverse01.original_four_word_unit_inputs_produce_the_actual_source_scaled_inverse_residue a b oddB unit
  rw [modulus] at inverse
  unfold sourceNormalizedInverseCoefficient
  rw [Int.mul_emod, original_rx2_signed_adjustments_preserve_the_entire_integer_scalar_modulus_residue, ←Int.mul_emod]
  exact inverse

set_option pp.all true in
#check @original_unsigned_wide_radix_is_exactly_two512
#print axioms original_unsigned_wide_radix_is_exactly_two512
set_option pp.all true in
#check @every_original_produced_inverse_coefficient_satisfies_both_signed_wide_bounds
#print axioms every_original_produced_inverse_coefficient_satisfies_both_signed_wide_bounds
set_option pp.all true in
#check @sourceNormalizedInverseCoefficient
#print axioms sourceNormalizedInverseCoefficient
set_option pp.all true in
#check @every_original_produced_inverse_coefficient_normalizes_to_the_full_unsigned_wide_range
#print axioms every_original_produced_inverse_coefficient_normalizes_to_the_full_unsigned_wide_range
set_option pp.all true in
#check @original_rx2_correction_shift_has_zero_entire_integer_scalar_modulus_residue
#print axioms original_rx2_correction_shift_has_zero_entire_integer_scalar_modulus_residue
set_option pp.all true in
#check @original_rx2_signed_adjustments_preserve_the_entire_integer_scalar_modulus_residue
#print axioms original_rx2_signed_adjustments_preserve_the_entire_integer_scalar_modulus_residue
set_option pp.all true in
#check @original_unit_scalar_inputs_produce_a_normalized_scaled_inverse_residue
#print axioms original_unit_scalar_inputs_produce_a_normalized_scaled_inverse_residue
end ShielddSecurity.TransferBlstArmInverseTopFixup01
