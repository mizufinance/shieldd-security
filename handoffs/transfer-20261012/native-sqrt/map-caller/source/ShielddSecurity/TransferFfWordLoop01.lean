import ShielddSecurity.TransferFfChoiceField01
import ShielddSecurity.FfFinishedPhase296
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferFfWordLoop01
open TransferBoundedNativeCodec01 (nullifierModulus)
open TransferSqrtProducerField01
open TransferSqrtProducerLoop01
open TransferFfChoiceField01
local instance scalarPrimeFact : Fact (Nat.Prime nullifierModulus) :=
  ⟨TransferScalarInverseCorrectness01.exact_source_scalar_modulus_is_prime⟩

def innerMeaning (s : SqrtInnerState) : FfFinishedPhase296.Inner (ZMod nullifierModulus) :=
  ⟨s.k.toNat,sourceFieldValue s.b2k,sourceFieldValue s.z,sourceBit s.jLessThanV⟩

def stateMeaning (s : SqrtState) : FfFinishedPhase296.State (ZMod nullifierModulus) :=
  ⟨sourceFieldValue s.x,sourceFieldValue s.b,sourceFieldValue s.z,s.v.toNat⟩

theorem exact_source_inner_step_has_the_field_and_unsigned_index_meaning
    (v : UInt32) (s : SqrtInnerState) (j : Nat) (bounded : j < UInt32.size) :
    innerMeaning (sourceSqrtInnerStep v s j) =
      FfFinishedPhase296.innerStep v.toNat (innerMeaning s) j := by
  by_cases one : sourceFieldValue s.b2k = 1 <;>
    simp [innerMeaning,sourceSqrtInnerStep,FfFinishedPhase296.innerStep,
    source_u32_masked_selection_has_the_exact_boolean_index_branch,
    source_scalar_equality_choice_has_the_exact_field_equality_bit,
    source_field_one_has_the_exact_mathematical_one,
    source_scalar_masked_selection_has_the_exact_boolean_field_branch,
    source_field_square_has_exact_ring_value,pow_two,
    source_choice_and_has_the_exact_boolean_conjunction,
    source_choice_not_has_the_exact_boolean_negation,
    source_u32_equality_choice_has_the_exact_unsigned_integer_equality_bit,
    UInt32.toNat_ofNat_of_lt' bounded,one]

theorem exact_source_inner_fold_has_the_field_and_unsigned_index_meaning
    (v : UInt32) (indices : List Nat) (bounded : ∀ j ∈ indices, j < UInt32.size) (s : SqrtInnerState) :
    innerMeaning (indices.foldl (sourceSqrtInnerStep v) s) =
      indices.foldl (FfFinishedPhase296.innerStep v.toNat) (innerMeaning s) := by
  induction indices generalizing s with
  | nil => rfl
  | cons j rest ih =>
    simp only [List.foldl_cons]
    rw [ih (fun n member => bounded n (List.mem_cons_of_mem j member)),
      exact_source_inner_step_has_the_field_and_unsigned_index_meaning v s j (bounded j List.mem_cons_self)]

theorem exact_source_inner_schedule_is_the_mathematical_range (maxV : Nat) :
    sourceSqrtInnerIndices maxV = List.range' 2 (maxV-2) := by
  simp only [sourceSqrtInnerIndices,List.range'_eq_map_range,Nat.add_comm]

theorem exact_source_round_has_the_field_and_unsigned_index_meaning
    (s : SqrtState) (maxV : Nat) (bounded : maxV ≤ 32) :
    stateMeaning (sourceSqrtRound s maxV) = FfFinishedPhase296.outerStep maxV (stateMeaning s) := by
  have indexBound : ∀ j ∈ sourceSqrtInnerIndices maxV, j < UInt32.size := by
    rw [exact_source_inner_schedule_is_the_mathematical_range]
    intro j member
    obtain ⟨offset,bound,equal⟩ := List.mem_range'.mp member
    have wordSize : UInt32.size = 4294967296 := rfl
    rw [wordSize,equal]
    omega
  let initial : SqrtInnerState := ⟨1,TransferScalarPowInvariant01.sourceCanonicalSquare s.b,s.z,
    TransferScalarChoiceMasks01.sourceChoiceFromBool true⟩
  have innerMatch : innerMeaning ((sourceSqrtInnerIndices maxV).foldl (sourceSqrtInnerStep s.v) initial) =
      FfFinishedPhase296.innerFor maxV (stateMeaning s) := by
    rw [exact_source_inner_fold_has_the_field_and_unsigned_index_meaning s.v _ indexBound initial,
      exact_source_inner_schedule_is_the_mathematical_range]
    simp [FfFinishedPhase296.innerFor,innerMeaning,initial,stateMeaning,
      source_field_square_has_exact_ring_value,pow_two,literal_source_bool_choice_has_the_exact_bit]
  unfold FfFinishedPhase296.outerStep
  rw [← innerMatch]
  simp [stateMeaning,sourceSqrtRound,innerMeaning,initial,
    source_field_multiply_has_exact_ring_value,source_field_square_has_exact_ring_value,pow_two,
    source_scalar_masked_selection_has_the_exact_boolean_field_branch,
    source_scalar_equality_choice_has_the_exact_field_equality_bit,
    source_field_one_has_the_exact_mathematical_one]

theorem exact_source_outer_fold_has_the_field_and_unsigned_index_meaning
    (rounds : List Nat) (bounded : ∀ maxV ∈ rounds, maxV ≤ 32) (s : SqrtState) :
    stateMeaning (rounds.foldl sourceSqrtRound s) =
      FfFinishedPhase296.outerLoop rounds (stateMeaning s) := by
  induction rounds generalizing s with
  | nil => rfl
  | cons maxV rest ih =>
    change stateMeaning (rest.foldl sourceSqrtRound (sourceSqrtRound s maxV)) =
      FfFinishedPhase296.outerLoop rest (FfFinishedPhase296.outerStep maxV (stateMeaning s))
    rw [ih (fun n member => bounded n (List.mem_cons_of_mem maxV member)),
      exact_source_round_has_the_field_and_unsigned_index_meaning s maxV (bounded maxV List.mem_cons_self)]

theorem actual_source_sqrt_loop_has_the_exact_field_and_unsigned_index_meaning
    (input : TransferCanonicalWordEquality01.CanonicalScalar) :
    stateMeaning (sourceSqrtFinalState input) =
      FfFinishedPhase296.outerLoop sourceSqrtOuterIndices (stateMeaning (sourceSqrtInitial input)) := by
  apply exact_source_outer_fold_has_the_field_and_unsigned_index_meaning
  decide

set_option pp.all true in
#check @scalarPrimeFact
#print axioms scalarPrimeFact
set_option pp.all true in
#check @innerMeaning
#print axioms innerMeaning
set_option pp.all true in
#check @stateMeaning
#print axioms stateMeaning
set_option pp.all true in
#check @exact_source_inner_step_has_the_field_and_unsigned_index_meaning
#print axioms exact_source_inner_step_has_the_field_and_unsigned_index_meaning
set_option pp.all true in
#check @exact_source_inner_fold_has_the_field_and_unsigned_index_meaning
#print axioms exact_source_inner_fold_has_the_field_and_unsigned_index_meaning
set_option pp.all true in
#check @exact_source_inner_schedule_is_the_mathematical_range
#print axioms exact_source_inner_schedule_is_the_mathematical_range
set_option pp.all true in
#check @exact_source_round_has_the_field_and_unsigned_index_meaning
#print axioms exact_source_round_has_the_field_and_unsigned_index_meaning
set_option pp.all true in
#check @exact_source_outer_fold_has_the_field_and_unsigned_index_meaning
#print axioms exact_source_outer_fold_has_the_field_and_unsigned_index_meaning
set_option pp.all true in
#check @actual_source_sqrt_loop_has_the_exact_field_and_unsigned_index_meaning
#print axioms actual_source_sqrt_loop_has_the_exact_field_and_unsigned_index_meaning
end ShielddSecurity.TransferFfWordLoop01
