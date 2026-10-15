import ShielddSecurity.TransferBlstArmInverseCanonicalUnit01
import ShielddSecurity.TransferScalarMontgomeryValue01
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseFieldIdentity01
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarSerializationRange01 (radix64)
open TransferScalarMontgomeryValue01 (radixInverse)
open TransferBlstArmInverseWordRepack01 (sourceFourWordsOfNat)
open TransferBlstArmInverseScaledInverse01 (sourceScaledInverseCoefficient)
attribute [local irreducible] sourceFourWordsOfNat sourceScaledInverseCoefficient

/-! The original produced integer coefficient gives the exact Montgomery
scaled field identity for every canonical nonzero raw input. The final lemma
consumes a weighted output relation, not a desired inverse conclusion.
Identification of the actual stored coefficient with this produced integer,
its signed range, and compiled execution remain separate obligations. -/

theorem the_original_two512_scale_is_the_square_of_the_four_word_montgomery_radix :
    (2 : ZMod nullifierModulus) ^ 512 =
      (radix64 ^ 4 : ZMod nullifierModulus) * (radix64 ^ 4 : ZMod nullifierModulus) := by
  simp only [radix64, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_add]

theorem the_original_radix_inverse_is_an_exact_field_left_inverse :
    (radixInverse : ZMod nullifierModulus) * (radix64 ^ 4 : ZMod nullifierModulus) = 1 := by
  have exactInverse := TransferScalarMontgomeryValue01.source_four_word_radix_inverse_is_exact
  have casted := congrArg (fun value : Nat => (value : ZMod nullifierModulus)) exactInverse
  simpa only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_one] using casted

theorem every_canonical_nonzero_source_scalar_produces_the_entire_montgomery_scaled_field_identity
    (input : Nat) (canonical : input < nullifierModulus) (nonzero : input ≠ 0) :
    (sourceScaledInverseCoefficient (sourceFourWordsOfNat input)
      (sourceFourWordsOfNat nullifierModulus) : ZMod nullifierModulus) * (input : ZMod nullifierModulus) =
        (radix64 ^ 4 : ZMod nullifierModulus) * (radix64 ^ 4 : ZMod nullifierModulus) := by
  have row := TransferBlstArmInverseCanonicalUnit01.every_canonical_nonzero_source_scalar_produces_the_entire_original_two512_bezout_identity
    input canonical nonzero
  have casted := congrArg (fun value : Int => (value : ZMod nullifierModulus)) row
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_ofNat,
    ZMod.natCast_self, mul_zero, add_zero] at casted
  exact casted.trans the_original_two512_scale_is_the_square_of_the_four_word_montgomery_radix

theorem the_produced_coefficient_and_weighted_output_relation_derive_the_entire_input_field_inverse
    (input : Nat) (canonical : input < nullifierModulus) (nonzero : input ≠ 0)
    (output : ZMod nullifierModulus)
    (weighted : (radix64 ^ 4 : ZMod nullifierModulus) * output =
      (sourceScaledInverseCoefficient (sourceFourWordsOfNat input)
        (sourceFourWordsOfNat nullifierModulus) : ZMod nullifierModulus)) :
    output * ((radixInverse : ZMod nullifierModulus) * (input : ZMod nullifierModulus)) = 1 := by
  have coefficient := every_canonical_nonzero_source_scalar_produces_the_entire_montgomery_scaled_field_identity
    input canonical nonzero
  have inverse := the_original_radix_inverse_is_an_exact_field_left_inverse
  calc
    output * ((radixInverse : ZMod nullifierModulus) * (input : ZMod nullifierModulus)) =
        ((radixInverse : ZMod nullifierModulus) * (radix64 ^ 4 : ZMod nullifierModulus)) *
          (output * ((radixInverse : ZMod nullifierModulus) * (input : ZMod nullifierModulus))) := by
      rw [inverse, one_mul]
    _ = ((radixInverse : ZMod nullifierModulus) * (radixInverse : ZMod nullifierModulus)) *
        (((radix64 ^ 4 : ZMod nullifierModulus) * output) * (input : ZMod nullifierModulus)) := by ring
    _ = ((radixInverse : ZMod nullifierModulus) * (radixInverse : ZMod nullifierModulus)) *
        ((radix64 ^ 4 : ZMod nullifierModulus) * (radix64 ^ 4 : ZMod nullifierModulus)) := by
      rw [weighted, coefficient]
    _ = ((radixInverse : ZMod nullifierModulus) * (radix64 ^ 4 : ZMod nullifierModulus)) *
        ((radixInverse : ZMod nullifierModulus) * (radix64 ^ 4 : ZMod nullifierModulus)) := by ring
    _ = 1 := by rw [inverse, one_mul]

set_option pp.all true in
#check @the_original_two512_scale_is_the_square_of_the_four_word_montgomery_radix
#print axioms the_original_two512_scale_is_the_square_of_the_four_word_montgomery_radix
set_option pp.all true in
#check @the_original_radix_inverse_is_an_exact_field_left_inverse
#print axioms the_original_radix_inverse_is_an_exact_field_left_inverse
set_option pp.all true in
#check @every_canonical_nonzero_source_scalar_produces_the_entire_montgomery_scaled_field_identity
#print axioms every_canonical_nonzero_source_scalar_produces_the_entire_montgomery_scaled_field_identity
set_option pp.all true in
#check @the_produced_coefficient_and_weighted_output_relation_derive_the_entire_input_field_inverse
#print axioms the_produced_coefficient_and_weighted_output_relation_derive_the_entire_input_field_inverse
end ShielddSecurity.TransferBlstArmInverseFieldIdentity01
