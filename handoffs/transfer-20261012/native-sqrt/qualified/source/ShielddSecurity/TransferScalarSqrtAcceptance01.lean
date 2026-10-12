import ShielddSecurity.TransferScalarPredicates01
import ShielddSecurity.TransferScalarFieldValues01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferScalarSqrtAcceptance01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarPowInvariant01 (sourceCanonicalMul)
open TransferScalarConstantEquality01 (sourceScalarWordsCtEqByte)
open TransferScalarPredicates01
/-! The locked ff::helpers::sqrt_tonelli_shanks final CtOption uses
`(x * x).ct_eq(f)`. Derive its bit invariant and acceptance/refusal mathematics
from the independently qualified word multiplication and equality operations.
The candidate is arbitrary in the explicit canonical source-model domain;
neither a correct-root premise nor a successful producer is supplied.
This is the final acceptance check only. Tonelli-Shanks candidate construction,
root existence/completeness, native private origins/Choice/CtOption/compiler/
ABI and complete Elligator/Transfer execution correspondence remain separate. -/

def sourceSqrtFinalChoiceByte (input candidate : CanonicalScalar) : UInt8 :=
  sourceScalarWordsCtEqByte (sourceCanonicalMul candidate candidate).words input.words

theorem source_sqrt_final_choice_has_derived_bit_invariant (input candidate : CanonicalScalar) :
    (sourceSqrtFinalChoiceByte input candidate).toNat < 2 := by
  exact source_scalar_equality_choice_byte_has_derived_bit_invariant _ _

theorem source_sqrt_final_choice_accepts_exactly_the_mathematical_square
    (input candidate : CanonicalScalar) :
    sourceSqrtFinalChoiceByte input candidate = 1 ↔
      (montgomeryValue candidate.words * montgomeryValue candidate.words) % nullifierModulus =
        montgomeryValue input.words := by
  have choice := valid_choice_source_boolean_conversion_is_exact_stored_byte_one
    (sourceSqrtFinalChoiceByte input candidate)
    (source_sqrt_final_choice_has_derived_bit_invariant input candidate)
  have equality := source_scalar_equality_boolean_has_exact_mathematical_field_meaning
    (sourceCanonicalMul candidate candidate) input
  have mathematics : sourceChoiceBool (sourceSqrtFinalChoiceByte input candidate) = true ↔
      (montgomeryValue candidate.words * montgomeryValue candidate.words) % nullifierModulus =
        montgomeryValue input.words := by
    simpa only [sourceSqrtFinalChoiceByte, sourceScalarEqualityBool,
      TransferScalarFieldValues01.actual_modeled_canonical_multiply_has_exact_mathematical_field_value] using equality
  exact choice.symm.trans mathematics

def sourceSqrtFinalOption (input candidate : CanonicalScalar) : Option CanonicalScalar :=
  if sourceSqrtFinalChoiceByte input candidate = 1 then some candidate else none

theorem every_source_sqrt_final_success_returns_the_checked_candidate_and_square
    (input candidate returned : CanonicalScalar)
    (success : sourceSqrtFinalOption input candidate = some returned) :
    returned = candidate ∧
      (montgomeryValue returned.words * montgomeryValue returned.words) % nullifierModulus =
        montgomeryValue input.words := by
  by_cases accepted : sourceSqrtFinalChoiceByte input candidate = 1
  · rw [sourceSqrtFinalOption, if_pos accepted] at success
    have same : candidate = returned := Option.some.inj success
    subst returned
    exact ⟨rfl, (source_sqrt_final_choice_accepts_exactly_the_mathematical_square input candidate).mp accepted⟩
  · rw [sourceSqrtFinalOption, if_neg accepted] at success
    cases success

theorem source_sqrt_final_refusal_is_exactly_failure_of_the_candidate_square
    (input candidate : CanonicalScalar) :
    sourceSqrtFinalOption input candidate = none ↔
      (montgomeryValue candidate.words * montgomeryValue candidate.words) % nullifierModulus ≠
        montgomeryValue input.words := by
  by_cases accepted : sourceSqrtFinalChoiceByte input candidate = 1
  · rw [sourceSqrtFinalOption, if_pos accepted]
    have square := (source_sqrt_final_choice_accepts_exactly_the_mathematical_square input candidate).mp accepted
    constructor
    · intro impossible
      cases impossible
    · intro notSquare
      exact False.elim (notSquare square)
  · rw [sourceSqrtFinalOption, if_neg accepted]
    have notSquare : (montgomeryValue candidate.words * montgomeryValue candidate.words) % nullifierModulus ≠
        montgomeryValue input.words := fun square => accepted
      ((source_sqrt_final_choice_accepts_exactly_the_mathematical_square input candidate).mpr square)
    exact ⟨fun _ => notSquare, fun _ => rfl⟩

set_option pp.all true in
#check @sourceSqrtFinalChoiceByte
#print axioms sourceSqrtFinalChoiceByte
set_option pp.all true in
#check @source_sqrt_final_choice_has_derived_bit_invariant
#print axioms source_sqrt_final_choice_has_derived_bit_invariant
set_option pp.all true in
#check @source_sqrt_final_choice_accepts_exactly_the_mathematical_square
#print axioms source_sqrt_final_choice_accepts_exactly_the_mathematical_square
set_option pp.all true in
#check @sourceSqrtFinalOption
#print axioms sourceSqrtFinalOption
set_option pp.all true in
#check @every_source_sqrt_final_success_returns_the_checked_candidate_and_square
#print axioms every_source_sqrt_final_success_returns_the_checked_candidate_and_square
set_option pp.all true in
#check @source_sqrt_final_refusal_is_exactly_failure_of_the_candidate_square
#print axioms source_sqrt_final_refusal_is_exactly_failure_of_the_candidate_square
end ShielddSecurity.TransferScalarSqrtAcceptance01
