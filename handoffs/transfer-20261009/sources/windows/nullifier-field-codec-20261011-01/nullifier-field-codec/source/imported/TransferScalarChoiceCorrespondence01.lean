import ShielddSecurity.TransferScalarChoiceMasks01
import ShielddSecurity.TransferScalarConstantEquality01
import ShielddSecurity.TransferScalarPowField01
import ShielddSecurity.TransferScalarInverseCorrectness01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarChoiceCorrespondence01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarPowInvariant01 (sourceZero sourceOne sourceCanonicalMul)
open TransferScalarInvertChain01 (sourceInvert sourceInvertPayload)
open TransferScalarChoiceMasks01 (sourceMaskedPow)
open TransferScalarConstantEquality01 (sourceInvertFlagByte)
/-! Pending source-model composition. Selection and equality dependencies must
first pass their own guarded qualification. No compiled Rust, volatile-barrier,
constant-time, native caller-origin, or full Transfer certification is implied.
The equality-derived byte replaces the abstract raw-word refusal branch, and
the exact word-mask power loop inherits the already derived field exponent. -/

theorem exact_word_masked_source_power_has_the_mathematical_field_value
    (self : CanonicalScalar) (exponent : Vector UInt64 4) :
    montgomeryValue (sourceMaskedPow self exponent).words =
      montgomeryValue self.words ^ packWords exponent.toList % nullifierModulus := by
  rw [TransferScalarChoiceMasks01.exact_source_word_masked_power_loop_equals_the_boolean_power_model]
  exact TransferScalarPowField01.exact_source_constant_time_pow_has_mathematical_little_endian_field_power self exponent

def sourceChoiceFlagInvert (self : CanonicalScalar) : Option CanonicalScalar :=
  if sourceInvertFlagByte self = 0 then none else sourceInvertPayload self

theorem exact_equality_derived_choice_byte_inversion_equals_the_qualified_source_model
    (self : CanonicalScalar) : sourceChoiceFlagInvert self = sourceInvert self := by
  rw [sourceChoiceFlagInvert,
    TransferScalarConstantEquality01.exact_source_invert_choice_flag_is_refusal_at_mathematical_zero]
  by_cases zero : self.words = sourceZero.words
  · have fieldZero := (TransferScalarInverseCorrectness01.canonical_source_scalar_has_zero_field_value_iff_exact_zero_words self).mpr zero
    rw [sourceInvert, if_pos fieldZero, if_pos zero]
    rfl
  · have fieldNonzero : montgomeryValue self.words ≠ 0 := by
      intro impossible
      exact zero ((TransferScalarInverseCorrectness01.canonical_source_scalar_has_zero_field_value_iff_exact_zero_words self).mp impossible)
    rw [sourceInvert, if_neg fieldNonzero, if_neg zero]
    rfl

theorem exact_equality_derived_choice_inversion_refuses_iff_the_field_value_is_zero
    (self : CanonicalScalar) :
    sourceChoiceFlagInvert self = none ↔ montgomeryValue self.words = 0 := by
  rw [exact_equality_derived_choice_byte_inversion_equals_the_qualified_source_model]
  exact TransferScalarInverseCorrectness01.exact_source_inversion_refuses_iff_mathematical_field_value_is_zero self

theorem exact_equality_derived_choice_returned_inversion_is_a_mathematical_inverse
    (self value : CanonicalScalar) (returned : sourceChoiceFlagInvert self = some value) :
    (montgomeryValue value.words * montgomeryValue self.words) % nullifierModulus = 1 := by
  rw [exact_equality_derived_choice_byte_inversion_equals_the_qualified_source_model] at returned
  exact TransferScalarInverseCorrectness01.exact_returned_source_inversion_is_a_mathematical_field_inverse self value returned

theorem exact_equality_derived_choice_returned_inverse_multiplies_to_raw_source_one
    (self value : CanonicalScalar) (returned : sourceChoiceFlagInvert self = some value) :
    (sourceCanonicalMul value self).words = sourceOne.words := by
  rw [exact_equality_derived_choice_byte_inversion_equals_the_qualified_source_model] at returned
  exact TransferScalarInverseCorrectness01.exact_returned_source_inverse_multiplication_has_exact_raw_one_words self value returned

set_option pp.all true in
#check @exact_word_masked_source_power_has_the_mathematical_field_value
#print axioms exact_word_masked_source_power_has_the_mathematical_field_value
set_option pp.all true in
#check @sourceChoiceFlagInvert
#print axioms sourceChoiceFlagInvert
set_option pp.all true in
#check @exact_equality_derived_choice_byte_inversion_equals_the_qualified_source_model
#print axioms exact_equality_derived_choice_byte_inversion_equals_the_qualified_source_model
set_option pp.all true in
#check @exact_equality_derived_choice_inversion_refuses_iff_the_field_value_is_zero
#print axioms exact_equality_derived_choice_inversion_refuses_iff_the_field_value_is_zero
set_option pp.all true in
#check @exact_equality_derived_choice_returned_inversion_is_a_mathematical_inverse
#print axioms exact_equality_derived_choice_returned_inversion_is_a_mathematical_inverse
set_option pp.all true in
#check @exact_equality_derived_choice_returned_inverse_multiplies_to_raw_source_one
#print axioms exact_equality_derived_choice_returned_inverse_multiplies_to_raw_source_one
end ShielddSecurity.TransferScalarChoiceCorrespondence01
