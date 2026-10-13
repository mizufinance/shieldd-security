import ShielddSecurity.TransferFfSqrtComplete01
import ShielddSecurity.TransferScalarCanonicalKey01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferFfFieldApi01
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferSqrtProducerField01
open TransferSqrtProducerLoop01
open TransferFfSqrtComplete01
local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩
local instance scalarNonzero : NeZero nullifierModulus := ⟨by decide⟩

/-- Exact existing source LE decoder constructs the canonical input words.
No arbitrary inverse codec or chosen root is supplied. -/
def fieldScalar (value : ZMod nullifierModulus) : CanonicalScalar :=
  TransferScalarCanonicalKey01.canonicalScalarForKey ⟨value.val,value.val_lt⟩

theorem actual_source_word_constructor_projects_to_every_field_input (value : ZMod nullifierModulus) :
    sourceFieldValue (fieldScalar value) = value := by
  unfold sourceFieldValue fieldScalar
  rw [← TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_has_exact_canonical_montgomery_value,
    TransferScalarCanonicalKey01.constructed_source_scalar_projects_to_exact_canonical_key]
  exact ZMod.natCast_zmod_val value

def sourceSdkFieldSqrt (input : ZMod nullifierModulus) : Option (ZMod nullifierModulus) :=
  (sourceSqrt (fieldScalar input)).map sourceFieldValue

theorem actual_source_sdk_field_sqrt_is_sound (input returned : ZMod nullifierModulus)
    (success : sourceSdkFieldSqrt input = some returned) : returned*returned = input := by
  cases observed : sourceSqrt (fieldScalar input) with
  | none => simp only [sourceSdkFieldSqrt,observed,Option.map_none,reduceCtorEq] at success
  | some candidate =>
    have same : sourceFieldValue candidate = returned := by
      simpa only [sourceSdkFieldSqrt,observed,Option.map_some,Option.some.injEq] using success
    have root := (every_returned_source_sqrt_is_its_actual_loop_payload_and_a_mathematical_root _ _ observed).2
    have field := congrArg (fun n : Nat => (n : ZMod nullifierModulus)) root
    have interpreted : sourceFieldValue candidate*sourceFieldValue candidate = sourceFieldValue (fieldScalar input) := by
      simpa only [sourceFieldValue,ZMod.natCast_mod,Nat.cast_mul] using field
    rw [same,actual_source_word_constructor_projects_to_every_field_input] at interpreted
    exact interpreted

theorem actual_source_sdk_field_sqrt_is_complete (input : ZMod nullifierModulus)
    (square : IsSquare input) : ∃ returned, sourceSdkFieldSqrt input = some returned := by
  have derivedSquare : IsSquare (sourceFieldValue (fieldScalar input)) := by
    simpa only [actual_source_word_constructor_projects_to_every_field_input] using square
  refine ⟨sourceFieldValue (sourceSqrtPayload (fieldScalar input)),?_⟩
  simp only [sourceSdkFieldSqrt,actual_ff_source_sqrt_is_complete_for_every_square _ derivedSquare,Option.map_some]

theorem actual_source_sdk_field_sqrt_has_the_total_square_contract (input : ZMod nullifierModulus) :
    (sourceSdkFieldSqrt input).isSome = true ↔ IsSquare input := by
  constructor
  · intro present
    cases observed : sourceSdkFieldSqrt input with
    | none => simp only [observed,Option.isSome_none,Bool.false_eq_true] at present
    | some root => exact ⟨root,(actual_source_sdk_field_sqrt_is_sound input root observed).symm⟩
  · intro square
    obtain ⟨returned,success⟩ := actual_source_sdk_field_sqrt_is_complete input square
    simp only [success,Option.isSome_some]

set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @scalarNonzero
#print axioms scalarNonzero
set_option pp.all true in
#check @fieldScalar
#print axioms fieldScalar
set_option pp.all true in
#check @actual_source_word_constructor_projects_to_every_field_input
#print axioms actual_source_word_constructor_projects_to_every_field_input
set_option pp.all true in
#check @sourceSdkFieldSqrt
#print axioms sourceSdkFieldSqrt
set_option pp.all true in
#check @actual_source_sdk_field_sqrt_is_sound
#print axioms actual_source_sdk_field_sqrt_is_sound
set_option pp.all true in
#check @actual_source_sdk_field_sqrt_is_complete
#print axioms actual_source_sdk_field_sqrt_is_complete
set_option pp.all true in
#check @actual_source_sdk_field_sqrt_has_the_total_square_contract
#print axioms actual_source_sdk_field_sqrt_has_the_total_square_contract
end ShielddSecurity.TransferFfFieldApi01
