import ShielddSecurity.TransferScalarInvertField01
import ShielddSecurity.FieldPrimeNode38
import Mathlib.FieldTheory.Finite.Basic
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarInverseCorrectness01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarPowInvariant01 (sourceZero sourceOne sourceCanonicalMul)
open TransferScalarInvertChain01 (sourceInvert sourceInvertPayload)
/-! Reuse the already qualified exact modulus primality certificate without
replay. Fermat connects the derived source-chain exponent with an actual
mathematical inverse. Canonical-value injectivity gives exact modeled raw ONE
after multiplication. Native Choice/library/compiler/caller binding is separate. -/

theorem exact_source_scalar_modulus_is_prime : Nat.Prime nullifierModulus :=
  FieldPrimeNode38.prime

theorem canonical_source_scalar_has_zero_field_value_iff_exact_zero_words (self : CanonicalScalar) :
    montgomeryValue self.words = 0 ↔ self.words = sourceZero.words := by
  have valueEquivalence := TransferCanonicalWordEquality01.canonical_internal_math_values_equal_iff_raw_words_equal self sourceZero
  rw [TransferScalarPowInvariant01.source_zero_and_one_constants_have_exact_canonical_montgomery_keys.1] at valueEquivalence
  exact valueEquivalence

theorem exact_prime_modulus_nonzero_field_power_is_a_multiplicative_inverse
    (base : Nat) (bounded : base < nullifierModulus) (nonzero : base ≠ 0) :
    (base ^ (nullifierModulus - 2) % nullifierModulus * base) % nullifierModulus = 1 := by
  letI : Fact (Nat.Prime nullifierModulus) := ⟨exact_source_scalar_modulus_is_prime⟩
  letI : NeZero nullifierModulus := ⟨by decide⟩
  have positive : (base : ZMod nullifierModulus) ≠ 0 := by
    intro zero
    have value := congrArg (fun x : ZMod nullifierModulus => x.val) zero
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt bounded, ZMod.val_zero] at value
    exact nonzero value
  have fermat := ZMod.pow_card_sub_one_eq_one positive
  have count : nullifierModulus - 2 + 1 = nullifierModulus - 1 := by decide
  have product : (base : ZMod nullifierModulus) ^ (nullifierModulus - 2) * (base : ZMod nullifierModulus) = 1 := by
    rw [← pow_succ, count]
    exact fermat
  have value := congrArg (fun x : ZMod nullifierModulus => x.val) product
  rw [← Nat.cast_pow, ← Nat.cast_mul, ZMod.val_natCast, ZMod.val_one] at value
  rw [Nat.mod_mul_mod]
  exact value

theorem exact_returned_source_inversion_is_a_mathematical_field_inverse
    (self value : CanonicalScalar) (returned : sourceInvert self = some value) :
    (montgomeryValue value.words * montgomeryValue self.words) % nullifierModulus = 1 := by
  by_cases zero : self.words = sourceZero.words
  · change (if self.words = sourceZero.words then none else sourceInvertPayload self) = some value at returned
    rw [if_pos zero] at returned
    cases returned
  · change (if self.words = sourceZero.words then none else sourceInvertPayload self) = some value at returned
    rw [if_neg zero] at returned
    rw [TransferScalarInvertField01.exact_source_invert_payload_has_modulus_minus_two_field_power self value returned]
    apply exact_prime_modulus_nonzero_field_power_is_a_multiplicative_inverse
    · unfold montgomeryValue
      exact Nat.mod_lt _ (by decide)
    · intro fieldZero
      exact zero ((canonical_source_scalar_has_zero_field_value_iff_exact_zero_words self).mp fieldZero)

theorem exact_returned_source_inverse_multiplication_has_exact_raw_one_words
    (self value : CanonicalScalar) (returned : sourceInvert self = some value) :
    (sourceCanonicalMul value self).words = sourceOne.words := by
  apply (TransferCanonicalWordEquality01.canonical_internal_math_values_equal_iff_raw_words_equal _ _).mp
  rw [TransferScalarFieldValues01.actual_modeled_canonical_multiply_has_exact_mathematical_field_value,
    exact_returned_source_inversion_is_a_mathematical_field_inverse self value returned,
    TransferScalarPowInvariant01.source_zero_and_one_constants_have_exact_canonical_montgomery_keys.2]

theorem exact_source_inversion_refuses_iff_mathematical_field_value_is_zero (self : CanonicalScalar) :
    sourceInvert self = none ↔ montgomeryValue self.words = 0 :=
  (TransferScalarInvertChain01.exact_source_invert_zero_refusal_is_derived self).trans
    (canonical_source_scalar_has_zero_field_value_iff_exact_zero_words self).symm

set_option pp.all true in
#check @exact_source_scalar_modulus_is_prime
#print axioms exact_source_scalar_modulus_is_prime
set_option pp.all true in
#check @canonical_source_scalar_has_zero_field_value_iff_exact_zero_words
#print axioms canonical_source_scalar_has_zero_field_value_iff_exact_zero_words
set_option pp.all true in
#check @exact_prime_modulus_nonzero_field_power_is_a_multiplicative_inverse
#print axioms exact_prime_modulus_nonzero_field_power_is_a_multiplicative_inverse
set_option pp.all true in
#check @exact_returned_source_inversion_is_a_mathematical_field_inverse
#print axioms exact_returned_source_inversion_is_a_mathematical_field_inverse
set_option pp.all true in
#check @exact_returned_source_inverse_multiplication_has_exact_raw_one_words
#print axioms exact_returned_source_inverse_multiplication_has_exact_raw_one_words
set_option pp.all true in
#check @exact_source_inversion_refuses_iff_mathematical_field_value_is_zero
#print axioms exact_source_inversion_refuses_iff_mathematical_field_value_is_zero
end ShielddSecurity.TransferScalarInverseCorrectness01
