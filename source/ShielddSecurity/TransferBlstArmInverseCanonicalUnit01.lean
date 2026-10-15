import ShielddSecurity.FieldPrimeNode38
import ShielddSecurity.TransferNullifierModulus01
import ShielddSecurity.TransferBlstArmInverseScaledInverse01
import Mathlib.Data.Nat.Prime.Basic
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferBlstArmInverseCanonicalUnit01
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferBlstArmInverseWindowSelect01 (sourcePackedFourWords)
open TransferBlstArmInverseWordRepack01 (sourceFourWordsOfNat)
open TransferBlstArmInverseScaledInverse01 (sourceScaledInverseCoefficient sourceScaledModulusCoefficient)
open TransferBlstArmInverseMagnitudeSchedule01 (sourceMagnitudeBatches)
open TransferBlstArmInverseFactors01 (sourceFactorWalk sourceFactorInitial)
attribute [local irreducible] sourceFourWordsOfNat sourcePackedFourWords
  sourceScaledInverseCoefficient sourceScaledModulusCoefficient sourceMagnitudeBatches sourceFactorWalk sourceFactorInitial

/-! Reuse the qualified exact scalar-modulus primality certificate. A
canonical nonzero natural input derives the unit-GCD premise of the full
source schedule and its scaled Bezout row. Runtime/private input origins,
stored coefficient construction and compiled execution remain open. -/

theorem every_canonical_nonzero_source_scalar_input_has_unit_gcd_with_the_exact_modulus
    (input : Nat) (canonical : input < nullifierModulus) (nonzero : input ≠ 0) :
    Nat.gcd input nullifierModulus = 1 := by
  have prime : Nat.Prime nullifierModulus := FieldPrimeNode38.prime
  exact (Nat.coprime_of_lt_prime nonzero canonical prime).symm

theorem every_canonical_source_input_and_the_exact_modulus_have_their_entire_original_word_repacking
    (input : Nat) (canonical : input < nullifierModulus) :
    sourcePackedFourWords (sourceFourWordsOfNat input) = input ∧
      sourcePackedFourWords (sourceFourWordsOfNat nullifierModulus) = nullifierModulus := by
  have modulusBound : nullifierModulus < 2 ^ 256 := by decide
  exact ⟨TransferBlstArmInverseWordRepack01.original_four_word_repacking_reconstructs_every_input_below_two256
      input (Nat.lt_trans canonical modulusBound),
    TransferBlstArmInverseWordRepack01.original_four_word_repacking_reconstructs_every_input_below_two256
      nullifierModulus modulusBound⟩

theorem the_exact_source_scalar_modulus_has_the_original_required_odd_low_word :
    (sourceFourWordsOfNat nullifierModulus).w0.toNat % 2 = 1 := by
  exact TransferBlstArmInverseWordRepack01.an_odd_natural_input_has_an_odd_original_repacked_low_word
    nullifierModulus (by decide)

theorem every_canonical_nonzero_source_scalar_finishes_the_original_fifteen_batch_and_exact47_schedule_at_zero_one
    (input : Nat) (canonical : input < nullifierModulus) (nonzero : input ≠ 0) :
    let final := sourceFactorWalk 47 (sourceFactorInitial
      (sourceMagnitudeBatches 15 (input, nullifierModulus)).1
      (sourceMagnitudeBatches 15 (input, nullifierModulus)).2)
    final.a = 0 ∧ final.b = 1 := by
  have words := every_canonical_source_input_and_the_exact_modulus_have_their_entire_original_word_repacking input canonical
  have unit := every_canonical_nonzero_source_scalar_input_has_unit_gcd_with_the_exact_modulus input canonical nonzero
  have packedUnit : Nat.gcd (sourcePackedFourWords (sourceFourWordsOfNat input))
      (sourcePackedFourWords (sourceFourWordsOfNat nullifierModulus)) = 1 := by rw [words.1, words.2]; exact unit
  have result := TransferBlstArmInverseScheduleUnit01.original_full_four_word_unit_inputs_finish_the_fifteen_batch_and_exact47_tail_at_zero_one
    (sourceFourWordsOfNat input) (sourceFourWordsOfNat nullifierModulus)
    the_exact_source_scalar_modulus_has_the_original_required_odd_low_word packedUnit
  rw [words.1, words.2] at result
  exact result

theorem every_canonical_nonzero_source_scalar_produces_the_entire_original_two512_bezout_identity
    (input : Nat) (canonical : input < nullifierModulus) (nonzero : input ≠ 0) :
    sourceScaledInverseCoefficient (sourceFourWordsOfNat input) (sourceFourWordsOfNat nullifierModulus) * (input : Int) +
      sourceScaledModulusCoefficient (sourceFourWordsOfNat input) (sourceFourWordsOfNat nullifierModulus) * (nullifierModulus : Int) =
        (2 : Int) ^ 512 := by
  have words := every_canonical_source_input_and_the_exact_modulus_have_their_entire_original_word_repacking input canonical
  have unit := every_canonical_nonzero_source_scalar_input_has_unit_gcd_with_the_exact_modulus input canonical nonzero
  have packedUnit : Nat.gcd (sourcePackedFourWords (sourceFourWordsOfNat input))
      (sourcePackedFourWords (sourceFourWordsOfNat nullifierModulus)) = 1 := by rw [words.1, words.2]; exact unit
  have result := TransferBlstArmInverseScaledInverse01.original_four_word_unit_inputs_produce_the_exact_two512_bezout_identity
    (sourceFourWordsOfNat input) (sourceFourWordsOfNat nullifierModulus)
    the_exact_source_scalar_modulus_has_the_original_required_odd_low_word packedUnit
  rw [words.1, words.2] at result
  exact result

theorem every_canonical_nonzero_source_scalar_produces_the_original_scaled_inverse_residue_without_a_supplied_unit_assumption
    (input : Nat) (canonical : input < nullifierModulus) (nonzero : input ≠ 0) :
    (sourceScaledInverseCoefficient (sourceFourWordsOfNat input) (sourceFourWordsOfNat nullifierModulus) * (input : Int)) % (nullifierModulus : Int) =
      (2 : Int) ^ 512 % (nullifierModulus : Int) := by
  exact TransferBlstArmInverseScaledInverse01.an_exact_integer_bezout_row_derives_the_scaled_inverse_residue _ _ _ _ _
    (every_canonical_nonzero_source_scalar_produces_the_entire_original_two512_bezout_identity input canonical nonzero)

set_option pp.all true in
#check @every_canonical_nonzero_source_scalar_input_has_unit_gcd_with_the_exact_modulus
#print axioms every_canonical_nonzero_source_scalar_input_has_unit_gcd_with_the_exact_modulus
set_option pp.all true in
#check @every_canonical_source_input_and_the_exact_modulus_have_their_entire_original_word_repacking
#print axioms every_canonical_source_input_and_the_exact_modulus_have_their_entire_original_word_repacking
set_option pp.all true in
#check @the_exact_source_scalar_modulus_has_the_original_required_odd_low_word
#print axioms the_exact_source_scalar_modulus_has_the_original_required_odd_low_word
set_option pp.all true in
#check @every_canonical_nonzero_source_scalar_finishes_the_original_fifteen_batch_and_exact47_schedule_at_zero_one
#print axioms every_canonical_nonzero_source_scalar_finishes_the_original_fifteen_batch_and_exact47_schedule_at_zero_one
set_option pp.all true in
#check @every_canonical_nonzero_source_scalar_produces_the_entire_original_two512_bezout_identity
#print axioms every_canonical_nonzero_source_scalar_produces_the_entire_original_two512_bezout_identity
set_option pp.all true in
#check @every_canonical_nonzero_source_scalar_produces_the_original_scaled_inverse_residue_without_a_supplied_unit_assumption
#print axioms every_canonical_nonzero_source_scalar_produces_the_original_scaled_inverse_residue_without_a_supplied_unit_assumption
end ShielddSecurity.TransferBlstArmInverseCanonicalUnit01
