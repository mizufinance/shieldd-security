import ShielddSecurity.TransferSqrtLoopPrimitives01
import ShielddSecurity.TransferScalarSqrtAcceptance01
import ShielddSecurity.TransferScalarCtOption01
import ShielddSecurity.TransferScalarPublicConstants01
import ShielddSecurity.TransferScalarPowField01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferSqrtProducerLoop01
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferScalarChoiceMasks01 (SourceChoiceByte sourceChoiceFromBool sourceMaskedScalarSelect)
open TransferScalarPowInvariant01 (sourceOne sourceCanonicalMul sourceCanonicalSquare sourcePowVartime)
open TransferScalarPublicConstants01 (sourceConstant)
open TransferScalarWordPrimitives01 (packWords)
open TransferScalarCtOption01 (SourceCtOption sourceCtOptionNew sourceCtOptionIntoOption)
open TransferSqrtLoopPrimitives01
open TransferScalarSqrtAcceptance01
/-! Exact locked ff0.13.0/bls12_3810.8.0 producer schedule, operations and
stored CtOption are modeled over the derived CanonicalScalar domain. Every
intermediate operation and Choice is derived from source primitives. No root
equation or producer-success premise is used to define any operation.
Returned-root soundness is proved; quadratic-residue completeness and the
Tonelli-Shanks progress invariant are distinct remaining obligations. Native
private origins, compiler/barrier/caller/ABI correspondence remain separate. -/

structure SqrtState where
  v : UInt32
  x : CanonicalScalar
  b : CanonicalScalar
  z : CanonicalScalar

structure SqrtInnerState where
  k : UInt32
  b2k : CanonicalScalar
  z : CanonicalScalar
  jLessThanV : SourceChoiceByte

def sourceSqrtExponent : Vector UInt64 4 :=
  #v[0x7fff_2dff_7fff_ffff, 0x04d0_ec02_a9de_d201,
    0x94ce_bea4_199c_ec04, 0x0000_0000_39f6_d3a9]

def sourceSqrtInitial (input : CanonicalScalar) : SqrtState :=
  let w := sourcePowVartime input sourceSqrtExponent
  let x := sourceCanonicalMul w input
  ⟨32, x, sourceCanonicalMul x w, sourceConstant .rootOfUnity⟩

def sourceSqrtInnerStep (v : UInt32) (state : SqrtInnerState) (j : Nat) : SqrtInnerState :=
  let b2kIsOne := sourceScalarEqChoice state.b2k sourceOne
  let squared := sourceCanonicalSquare (sourceMaskedScalarSelect state.b2k state.z b2kIsOne)
  let b2k := sourceMaskedScalarSelect squared state.b2k b2kIsOne
  let newZ := sourceMaskedScalarSelect state.z squared b2kIsOne
  let jLessThanV := sourceAndChoice state.jLessThanV (sourceNotChoice (sourceU32EqChoice (UInt32.ofNat j) v))
  let k := sourceU32Select (UInt32.ofNat j) state.k b2kIsOne
  let z := sourceMaskedScalarSelect state.z newZ jLessThanV
  ⟨k,b2k,z,jLessThanV⟩

def sourceSqrtInnerIndices (maxV : Nat) : List Nat := (List.range (maxV - 2)).map (· + 2)

def sourceSqrtRound (state : SqrtState) (maxV : Nat) : SqrtState :=
  let inner := (sourceSqrtInnerIndices maxV).foldl (sourceSqrtInnerStep state.v)
    ⟨1,sourceCanonicalSquare state.b,state.z,sourceChoiceFromBool true⟩
  let result := sourceCanonicalMul state.x inner.z
  let x := sourceMaskedScalarSelect result state.x (sourceScalarEqChoice state.b sourceOne)
  let z := sourceCanonicalSquare inner.z
  let b := sourceCanonicalMul state.b z
  ⟨inner.k,x,b,z⟩

def sourceSqrtOuterIndices : List Nat := (List.range 32).reverse.map (· + 1)

def sourceSqrtFinalState (input : CanonicalScalar) : SqrtState :=
  sourceSqrtOuterIndices.foldl sourceSqrtRound (sourceSqrtInitial input)

def sourceSqrtPayload (input : CanonicalScalar) : CanonicalScalar := (sourceSqrtFinalState input).x

def sourceSqrtCtOption (input : CanonicalScalar) : SourceCtOption CanonicalScalar :=
  let candidate := sourceSqrtPayload input
  sourceCtOptionNew candidate (sourceSqrtFinalChoiceByte input candidate)

def sourceSqrt (input : CanonicalScalar) : Option CanonicalScalar :=
  sourceCtOptionIntoOption (sourceSqrtCtOption input)

theorem source_sqrt_exponent_and_two_adicity_match_the_locked_scalar_parameters :
    packWords sourceSqrtExponent.toList = ((nullifierModulus - 1) / 2 ^ 32 - 1) / 2 ∧
      nullifierModulus - 1 = ((nullifierModulus - 1) / 2 ^ 32) * 2 ^ 32 ∧
      ((nullifierModulus - 1) / 2 ^ 32) % 2 = 1 := by decide

theorem source_sqrt_schedule_has_exact_32_outer_and_465_inner_iterations :
    sourceSqrtOuterIndices.length = 32 ∧
      (sourceSqrtOuterIndices.map (fun maxV => (sourceSqrtInnerIndices maxV).length)).sum = 465 := by decide

theorem source_sqrt_initial_power_has_exact_mathematical_exponent (input : CanonicalScalar) :
    montgomeryValue (sourcePowVartime input sourceSqrtExponent).words =
      montgomeryValue input.words ^ (((nullifierModulus - 1) / 2 ^ 32 - 1) / 2) % nullifierModulus := by
  rw [TransferScalarPowField01.exact_source_variable_time_pow_has_mathematical_little_endian_field_power,
    source_sqrt_exponent_and_two_adicity_match_the_locked_scalar_parameters.1]

theorem source_sqrt_producer_derives_canonical_payload_and_valid_stored_flag (input : CanonicalScalar) :
    packWords (sourceSqrtCtOption input).value.words.toList < nullifierModulus ∧
      (sourceSqrtCtOption input).isSomeByte.toNat < 2 := by
  exact ⟨(sourceSqrtPayload input).canonical, source_sqrt_final_choice_has_derived_bit_invariant input _⟩

theorem source_sqrt_producer_returns_exactly_its_qualified_final_check (input : CanonicalScalar) :
    sourceSqrt input = sourceSqrtFinalOption input (sourceSqrtPayload input) := by rfl

theorem every_returned_source_sqrt_is_its_actual_loop_payload_and_a_mathematical_root
    (input returned : CanonicalScalar) (success : sourceSqrt input = some returned) :
    returned = sourceSqrtPayload input ∧
      (montgomeryValue returned.words * montgomeryValue returned.words) % nullifierModulus = montgomeryValue input.words := by
  rw [source_sqrt_producer_returns_exactly_its_qualified_final_check] at success
  exact every_source_sqrt_final_success_returns_the_checked_candidate_and_square _ _ _ success

theorem source_sqrt_producer_refuses_exactly_when_its_actual_payload_is_not_a_root (input : CanonicalScalar) :
    sourceSqrt input = none ↔
      (montgomeryValue (sourceSqrtPayload input).words * montgomeryValue (sourceSqrtPayload input).words) %
        nullifierModulus ≠ montgomeryValue input.words := by
  rw [source_sqrt_producer_returns_exactly_its_qualified_final_check]
  exact source_sqrt_final_refusal_is_exactly_failure_of_the_candidate_square _ _

theorem source_sqrt_producer_accepts_exactly_when_its_actual_payload_is_a_root (input : CanonicalScalar) :
    (∃ returned, sourceSqrt input = some returned) ↔
      (montgomeryValue (sourceSqrtPayload input).words * montgomeryValue (sourceSqrtPayload input).words) %
        nullifierModulus = montgomeryValue input.words := by
  constructor
  · rintro ⟨returned,success⟩
    obtain ⟨same,root⟩ := every_returned_source_sqrt_is_its_actual_loop_payload_and_a_mathematical_root _ _ success
    simpa only [same] using root
  · intro root
    refine ⟨sourceSqrtPayload input,?_⟩
    rw [source_sqrt_producer_returns_exactly_its_qualified_final_check, sourceSqrtFinalOption,
      if_pos ((source_sqrt_final_choice_accepts_exactly_the_mathematical_square _ _).mpr root)]

set_option pp.all true in
#check @SqrtState
#print axioms SqrtState
set_option pp.all true in
#check @SqrtInnerState
#print axioms SqrtInnerState
set_option pp.all true in
#check @sourceSqrtExponent
#print axioms sourceSqrtExponent
set_option pp.all true in
#check @sourceSqrtInitial
#print axioms sourceSqrtInitial
set_option pp.all true in
#check @sourceSqrtInnerStep
#print axioms sourceSqrtInnerStep
set_option pp.all true in
#check @sourceSqrtInnerIndices
#print axioms sourceSqrtInnerIndices
set_option pp.all true in
#check @sourceSqrtRound
#print axioms sourceSqrtRound
set_option pp.all true in
#check @sourceSqrtOuterIndices
#print axioms sourceSqrtOuterIndices
set_option pp.all true in
#check @sourceSqrtFinalState
#print axioms sourceSqrtFinalState
set_option pp.all true in
#check @sourceSqrtPayload
#print axioms sourceSqrtPayload
set_option pp.all true in
#check @sourceSqrtCtOption
#print axioms sourceSqrtCtOption
set_option pp.all true in
#check @sourceSqrt
#print axioms sourceSqrt
set_option pp.all true in
#check @source_sqrt_exponent_and_two_adicity_match_the_locked_scalar_parameters
#print axioms source_sqrt_exponent_and_two_adicity_match_the_locked_scalar_parameters
set_option pp.all true in
#check @source_sqrt_schedule_has_exact_32_outer_and_465_inner_iterations
#print axioms source_sqrt_schedule_has_exact_32_outer_and_465_inner_iterations
set_option pp.all true in
#check @source_sqrt_initial_power_has_exact_mathematical_exponent
#print axioms source_sqrt_initial_power_has_exact_mathematical_exponent
set_option pp.all true in
#check @source_sqrt_producer_derives_canonical_payload_and_valid_stored_flag
#print axioms source_sqrt_producer_derives_canonical_payload_and_valid_stored_flag
set_option pp.all true in
#check @source_sqrt_producer_returns_exactly_its_qualified_final_check
#print axioms source_sqrt_producer_returns_exactly_its_qualified_final_check
set_option pp.all true in
#check @every_returned_source_sqrt_is_its_actual_loop_payload_and_a_mathematical_root
#print axioms every_returned_source_sqrt_is_its_actual_loop_payload_and_a_mathematical_root
set_option pp.all true in
#check @source_sqrt_producer_refuses_exactly_when_its_actual_payload_is_not_a_root
#print axioms source_sqrt_producer_refuses_exactly_when_its_actual_payload_is_not_a_root
set_option pp.all true in
#check @source_sqrt_producer_accepts_exactly_when_its_actual_payload_is_a_root
#print axioms source_sqrt_producer_accepts_exactly_when_its_actual_payload_is_a_root
end ShielddSecurity.TransferSqrtProducerLoop01
