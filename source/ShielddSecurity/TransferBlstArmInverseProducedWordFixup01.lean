import ShielddSecurity.TransferBlstArmInverseCoefficientEncoding01
import ShielddSecurity.TransferBlstArmInverseSecond01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseProducedWordFixup01
open TransferBlstArmInverseWindowSelect01 (SourceFourWords sourcePackedFourWords)
open TransferBlstArmInverseScaledInverse01 (sourceScaledInverseCoefficient)
open TransferBlstArmInverseTopFixup01 (sourceNormalizedInverseCoefficient)
open TransferBlstArmInverseCoefficientEncoding01 (sourceCoefficientWideState)
open TransferBlstArmInverseFirst01 (WideState sourceWideMeaning sourceWideRaw sourceFirstWordCorrection)
open TransferBlstArmInverseSecond01 (sourceSecondWordCorrection)
open TransferBlstArmInverseSign01 (sourceWideRadix)
open TransferBoundedNativeCodec01 (nullifierModulus)

/-! Feed the derived full source coefficient, explicitly encoded into the
original low/high/top state, through the original word adjustments. This
does not establish that native coefficient multiplication constructs the
encoding, or that the compiled ISA executes these source operations. -/

def sourceProducedCoefficientState (a b : SourceFourWords) : WideState :=
  sourceCoefficientWideState (sourceScaledInverseCoefficient a b)

def sourceProducedCorrectedCoefficientState (a b : SourceFourWords) : WideState :=
  sourceSecondWordCorrection (sourceFirstWordCorrection (sourceProducedCoefficientState a b))

theorem produced_coefficient_state_encoding_has_the_entire_derived_source_coefficient
    (a b : SourceFourWords) : sourceWideMeaning (sourceProducedCoefficientState a b) = sourceScaledInverseCoefficient a b := by
  exact TransferBlstArmInverseCoefficientEncoding01.every_integer_coefficient_encoding_has_the_entire_original_signed_wide_meaning _

theorem original_word_adjustments_of_the_encoded_produced_coefficient_derive_the_entire_normalized_integer
    (a b : SourceFourWords) : sourceWideMeaning (sourceProducedCorrectedCoefficientState a b) = sourceNormalizedInverseCoefficient a b := by
  have bounded := TransferBlstArmInverseTopFixup01.every_original_produced_inverse_coefficient_satisfies_both_signed_wide_bounds a b
  have encoded := produced_coefficient_state_encoding_has_the_entire_derived_source_coefficient a b
  have corrected := TransferBlstArmInverseSecond01.original_complete_two_word_adjustments_are_the_qualified_integer_signed_correction
    (sourceProducedCoefficientState a b) (by rw [encoded]; exact bounded.1) (by rw [encoded]; exact bounded.2)
  rw [encoded] at corrected
  exact corrected

theorem original_word_adjustments_of_the_encoded_produced_coefficient_store_the_entire_unsigned_normalized_integer
    (a b : SourceFourWords) : (sourceWideRaw (sourceProducedCorrectedCoefficientState a b) : Int) = sourceNormalizedInverseCoefficient a b := by
  have corrected := original_word_adjustments_of_the_encoded_produced_coefficient_derive_the_entire_normalized_integer a b
  have top : (sourceProducedCorrectedCoefficientState a b).2.2 = 0 := by rfl
  rw [sourceWideMeaning, top, Int.mul_zero, Int.add_zero] at corrected
  exact corrected

theorem original_word_adjustments_of_the_encoded_produced_coefficient_derive_the_full_unsigned_output_range
    (a b : SourceFourWords) :
    0 ≤ (sourceWideRaw (sourceProducedCorrectedCoefficientState a b) : Int) ∧
      (sourceWideRaw (sourceProducedCorrectedCoefficientState a b) : Int) < sourceWideRadix := by
  rw [original_word_adjustments_of_the_encoded_produced_coefficient_store_the_entire_unsigned_normalized_integer]
  exact TransferBlstArmInverseTopFixup01.every_original_produced_inverse_coefficient_normalizes_to_the_full_unsigned_wide_range a b

theorem original_word_adjustments_of_the_encoded_unit_scalar_coefficient_derive_the_stored_scaled_inverse_residue
    (a b : SourceFourWords) (oddB : b.w0.toNat % 2 = 1)
    (modulus : sourcePackedFourWords b = nullifierModulus)
    (unit : Nat.gcd (sourcePackedFourWords a) (sourcePackedFourWords b) = 1) :
    ((sourceWideRaw (sourceProducedCorrectedCoefficientState a b) : Int) * (sourcePackedFourWords a : Int)) % (nullifierModulus : Int) =
      (2 : Int) ^ 512 % (nullifierModulus : Int) := by
  rw [original_word_adjustments_of_the_encoded_produced_coefficient_store_the_entire_unsigned_normalized_integer]
  exact TransferBlstArmInverseTopFixup01.original_unit_scalar_inputs_produce_a_normalized_scaled_inverse_residue a b oddB modulus unit

set_option pp.all true in
#check @sourceProducedCoefficientState
#print axioms sourceProducedCoefficientState
set_option pp.all true in
#check @sourceProducedCorrectedCoefficientState
#print axioms sourceProducedCorrectedCoefficientState
set_option pp.all true in
#check @produced_coefficient_state_encoding_has_the_entire_derived_source_coefficient
#print axioms produced_coefficient_state_encoding_has_the_entire_derived_source_coefficient
set_option pp.all true in
#check @original_word_adjustments_of_the_encoded_produced_coefficient_derive_the_entire_normalized_integer
#print axioms original_word_adjustments_of_the_encoded_produced_coefficient_derive_the_entire_normalized_integer
set_option pp.all true in
#check @original_word_adjustments_of_the_encoded_produced_coefficient_store_the_entire_unsigned_normalized_integer
#print axioms original_word_adjustments_of_the_encoded_produced_coefficient_store_the_entire_unsigned_normalized_integer
set_option pp.all true in
#check @original_word_adjustments_of_the_encoded_produced_coefficient_derive_the_full_unsigned_output_range
#print axioms original_word_adjustments_of_the_encoded_produced_coefficient_derive_the_full_unsigned_output_range
set_option pp.all true in
#check @original_word_adjustments_of_the_encoded_unit_scalar_coefficient_derive_the_stored_scaled_inverse_residue
#print axioms original_word_adjustments_of_the_encoded_unit_scalar_coefficient_derive_the_stored_scaled_inverse_residue
end ShielddSecurity.TransferBlstArmInverseProducedWordFixup01
