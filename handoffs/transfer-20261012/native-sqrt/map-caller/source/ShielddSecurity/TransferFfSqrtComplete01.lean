import ShielddSecurity.TransferFfWordLoop01
import ShielddSecurity.TransferFfActiveCompleteness01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferFfSqrtComplete01
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferSqrtProducerLoop01
open TransferSqrtProducerField01
open TransferFfWordLoop01
open TransferFfActiveCompleteness01
local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩

theorem every_nonzero_square_derives_the_actual_source_initial_ready_state
    (input : CanonicalScalar) (nonzero : sourceFieldValue input ≠ 0)
    (square : IsSquare (sourceFieldValue input)) :
    Ready (sourceFieldValue input) 32 (stateMeaning (sourceSqrtInitial input)) := by
  right
  refine ⟨⟨by change 1 < 32; decide,?_,?_,?_,?_⟩,by change 32 ≤ 32; decide⟩
  · exact source_sqrt_initial_candidate_square_equals_input_times_initial_residue input
  · exact every_nonzero_square_input_derives_the_initial_half_order_bound input nonzero square
  · exact source_root_of_unity_has_exact_power_and_half_power.1
  · exact source_root_of_unity_has_exact_power_and_half_power.2

theorem every_nonzero_square_derives_an_actual_source_loop_root
    (input : CanonicalScalar) (nonzero : sourceFieldValue input ≠ 0)
    (square : IsSquare (sourceFieldValue input)) :
    sourceFieldValue (sourceSqrtPayload input) ^ 2 = sourceFieldValue input := by
  have finished := exact_descending_outer_loop_finishes_every_ready_state (sourceFieldValue input) 32
    (stateMeaning (sourceSqrtInitial input))
    (every_nonzero_square_derives_the_actual_source_initial_ready_state input nonzero square)
  have projection := actual_source_sqrt_loop_has_the_exact_field_and_unsigned_index_meaning input
  change stateMeaning (sourceSqrtFinalState input) =
    FfFinishedPhase296.outerLoop (descendingRounds 32) (stateMeaning (sourceSqrtInitial input)) at projection
  rw [← projection] at finished
  simpa only [stateMeaning,sourceSqrtPayload,pow_two] using finished.1

theorem every_square_derives_an_actual_source_loop_root (input : CanonicalScalar)
    (square : IsSquare (sourceFieldValue input)) :
    sourceFieldValue (sourceSqrtPayload input) ^ 2 = sourceFieldValue input := by
  by_cases zero : sourceFieldValue input = 0
  · have numerical := (source_field_value_zero_is_exact_mathematical_zero input).mp zero
    have payload := source_sqrt_of_mathematical_zero_derives_a_zero_loop_payload input zero
    simp only [payload,zero,zero_pow (by decide : 2 ≠ 0)]
  · exact every_nonzero_square_derives_an_actual_source_loop_root input zero square

theorem every_square_derives_the_actual_source_payload_numerical_square (input : CanonicalScalar)
    (square : IsSquare (sourceFieldValue input)) :
    (montgomeryValue (sourceSqrtPayload input).words * montgomeryValue (sourceSqrtPayload input).words) %
      nullifierModulus = montgomeryValue input.words := by
  have root := every_square_derives_an_actual_source_loop_root input square
  have exactWords := (source_field_value_equality_is_exact_word_equality
      (TransferScalarPowInvariant01.sourceCanonicalMul (sourceSqrtPayload input) (sourceSqrtPayload input)) input).mp
    (by simpa only [source_field_multiply_has_exact_ring_value,pow_two] using root)
  have value := congrArg montgomeryValue exactWords
  simpa only [TransferScalarFieldValues01.actual_modeled_canonical_multiply_has_exact_mathematical_field_value] using value

theorem actual_ff_source_sqrt_is_complete_for_every_square (input : CanonicalScalar)
    (square : IsSquare (sourceFieldValue input)) :
    sourceSqrt input = some (sourceSqrtPayload input) := by
  have root := every_square_derives_the_actual_source_payload_numerical_square input square
  rw [source_sqrt_producer_returns_exactly_its_qualified_final_check,
    TransferScalarSqrtAcceptance01.sourceSqrtFinalOption,
    if_pos ((TransferScalarSqrtAcceptance01.source_sqrt_final_choice_accepts_exactly_the_mathematical_square _ _).mpr root)]

theorem actual_ff_source_sqrt_accepts_exactly_the_mathematical_squares (input : CanonicalScalar) :
    (∃ returned, sourceSqrt input = some returned) ↔ IsSquare (sourceFieldValue input) := by
  constructor
  · rintro ⟨returned,success⟩
    obtain ⟨_,root⟩ := every_returned_source_sqrt_is_its_actual_loop_payload_and_a_mathematical_root input returned success
    refine ⟨sourceFieldValue returned,?_⟩
    unfold sourceFieldValue
    have field := congrArg (fun n : Nat => (n : ZMod nullifierModulus)) root
    simpa only [ZMod.natCast_mod,Nat.cast_mul] using field.symm
  · intro square
    exact ⟨sourceSqrtPayload input,actual_ff_source_sqrt_is_complete_for_every_square input square⟩

set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @every_nonzero_square_derives_the_actual_source_initial_ready_state
#print axioms every_nonzero_square_derives_the_actual_source_initial_ready_state
set_option pp.all true in
#check @every_nonzero_square_derives_an_actual_source_loop_root
#print axioms every_nonzero_square_derives_an_actual_source_loop_root
set_option pp.all true in
#check @every_square_derives_an_actual_source_loop_root
#print axioms every_square_derives_an_actual_source_loop_root
set_option pp.all true in
#check @every_square_derives_the_actual_source_payload_numerical_square
#print axioms every_square_derives_the_actual_source_payload_numerical_square
set_option pp.all true in
#check @actual_ff_source_sqrt_is_complete_for_every_square
#print axioms actual_ff_source_sqrt_is_complete_for_every_square
set_option pp.all true in
#check @actual_ff_source_sqrt_accepts_exactly_the_mathematical_squares
#print axioms actual_ff_source_sqrt_accepts_exactly_the_mathematical_squares
end ShielddSecurity.TransferFfSqrtComplete01
