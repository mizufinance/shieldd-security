import ShielddSecurity.TransferWordStageNumericRefinement01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCheckedWordStageRefinement01
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
open TransferStateDelta
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferCanonicalWordPending01 (decodeWordPending)
open TransferWordObjectCodec01 (WordTaggedObject decodeNative)
open TransferPendingFiniteCodec01 (restore)
open TransferNullifierBatchSource01 (Pending Backend BatchError uniqueLoop inspect appendPending)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferWordStageOrder01 (stageFields)
open TransferWordObjectRead01 (checkedObject)
open TransferWordStageNumericRefinement01 (installTypedPending typedDurableReader)
open TransferNullifierReaderVector01 (contains zipUnspent)
open TransferNullifierConsensusLimits01 (blockCapacity)
/-! Semantic result refinement for every prior source-shaped object branch.
Duplicate refusal occurs before typed access; wrong-type panic is retained as
an outer error. Only returned typed/default branches use the numeric pending
projection. Its old Other/default clause is not a native getter interpretation:
checked access prevents that clause from participating in successful staging.
Concrete modeled durable reader captures actual projected previous membership.
The numeric wrapper repeats the pure uniqueness check inside inspection; this
is result equality, not an identical native execution trace. Native Any/Ord/
Scalar/reader/usize/compiler/async/delta and full trace bindings remain OPEN.
No native/control/certification or accepted ancestor replay credit. -/

def projectObjectPending {Other : Type} (object : WordTaggedObject Other) : Pending :=
  restore (decodeNative object)

def previousPending {Other : Type} : Option (WordTaggedObject Other) → Pending
  | none => restore (.opened [] [])
  | some object => projectObjectPending object

def readerForPrevious {Other : Type} (gate : Bool) (lookup : Nat → Option Bool)
    (previous : Option (WordTaggedObject Other)) (inputs : List CanonicalScalar) : Except BatchError Unit :=
  let keys := inputs.map (fun scalar => scalarKey scalar.words)
  match contains gate lookup (previousPending previous).membership keys with
  | none => .error .reader
  | some flags => if zipUnspent keys flags then .ok () else .error .spent

def checkedNumericStage {O E Other : Type} (backend : Backend O E) (child : Delta O E)
    (previous : Option (WordTaggedObject Other)) (inputs : List CanonicalScalar) : Except Unit (Except BatchError Pending) :=
  let keys := inputs.map (fun scalar => scalarKey scalar.words)
  if uniqueLoop [] keys then
    match checkedObject previous with
    | .error panic => .error panic
    | .ok _ => .ok (inspect {backend with pending := fun _ => previousPending previous}
      (2 ^ 64 - 1) blockCapacity child keys)
  else .ok (.error .duplicate)

theorem projected_original_word_append_is_exact_numeric_pending_append {Other : Type}
    (ordered members inputs : List CanonicalScalar) :
    projectObjectPending (Other := Other) (.inl (.opened (ordered ++ inputs) (members ++ inputs))) =
      appendPending (restore (decodeWordPending (.opened ordered members)))
        (inputs.map (fun scalar => scalarKey scalar.words)) := by
  change restore (.opened ((ordered ++ inputs).map (fun scalar => scalarKey scalar.words))
      ((members ++ inputs).map (fun scalar => scalarKey scalar.words))) = _
  rw [List.map_append, List.map_append]
  exact TransferPendingFiniteCodec01.native_open_append_simulates_model_membership_union
    (ordered.map (fun scalar => scalarKey scalar.words)) (members.map (fun scalar => scalarKey scalar.words))
    (inputs.map (fun scalar => scalarKey scalar.words))

theorem numeric_inspection_recovers_after_original_field_write_and_projection {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (ordered members inputs : List CanonicalScalar) :
    ((inspect (installTypedPending backend ordered members) (2 ^ 64 - 1) blockCapacity child
      (inputs.map (fun scalar => scalarKey scalar.words))).map
      (fun _ => (.inl (.opened (ordered ++ inputs) (members ++ inputs)) : WordTaggedObject Other))).map projectObjectPending =
      inspect (installTypedPending backend ordered members) (2 ^ 64 - 1) blockCapacity child
        (inputs.map (fun scalar => scalarKey scalar.words)) := by
  cases inspected : inspect (installTypedPending backend ordered members) (2 ^ 64 - 1) blockCapacity child
      (inputs.map (fun scalar => scalarKey scalar.words)) with
  | error refusal => rfl
  | ok next =>
    obtain ⟨previous, _, previousEq, _, _, _, _, _, _, nextEq⟩ :=
      TransferNullifierBatchSource01.inspection_success_order (installTypedPending backend ordered members)
        (2 ^ 64 - 1) blockCapacity child (inputs.map (fun scalar => scalarKey scalar.words)) next inspected
    have appendEq : next = appendPending (restore (decodeWordPending (.opened ordered members)))
        (inputs.map (fun scalar => scalarKey scalar.words)) :=
      nextEq.trans (congrArg (fun pending : Pending => appendPending pending (inputs.map (fun scalar => scalarKey scalar.words))) previousEq)
    exact congrArg Except.ok ((projected_original_word_append_is_exact_numeric_pending_append
      (Other := Other) ordered members inputs).trans appendEq.symm)

theorem every_checked_source_stage_outcome_projects_to_checked_numeric_stage {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (previous : Option (WordTaggedObject Other))
    (inputs : List CanonicalScalar) :
    (stageFields previous inputs true (readerForPrevious (backend.readerGate child) (backend.lookup child) previous)).map
      (fun result => result.map projectObjectPending) = checkedNumericStage backend child previous inputs := by
  have typed (ordered members : List CanonicalScalar) :
      (stageFields (Other := Other) (some (.inl (.opened ordered members))) inputs true
        (readerForPrevious (backend.readerGate child) (backend.lookup child) (some (.inl (.opened ordered members))))).map
          (fun result => result.map projectObjectPending) =
        checkedNumericStage backend child (some (.inl (.opened ordered members))) inputs := by
    have wrapped : checkedNumericStage backend child (some (.inl (.opened ordered members))) inputs =
        .ok (inspect (installTypedPending backend ordered members) (2 ^ 64 - 1) blockCapacity child
          (inputs.map (fun scalar => scalarKey scalar.words))) := by
      unfold checkedNumericStage
      cases unique : uniqueLoop [] (inputs.map (fun scalar => scalarKey scalar.words)) with
      | false => simp only [Bool.false_eq_true, if_false, inspect, unique] <;> rfl
      | true => simp only [if_true, checkedObject] <;> rfl
    rw [wrapped]
    change (stageFields (some (.inl (.opened ordered members))) inputs true
      (typedDurableReader (backend.readerGate child) (backend.lookup child) members)).map
        (fun result => result.map projectObjectPending) = _
    rw [TransferWordStageNumericRefinement01.typed_open_stage_has_exact_numeric_inspection_result_and_original_field_write]
    exact congrArg Except.ok (numeric_inspection_recovers_after_original_field_write_and_projection
      (Other := Other) backend child ordered members inputs)
  cases previous with
  | none => exact typed [] []
  | some object =>
    cases object with
    | inr other =>
      unfold stageFields checkedNumericStage
      cases uniqueLoop [] (inputs.map (fun scalar => scalarKey scalar.words)) <;> rfl
    | inl pending =>
      cases pending with
      | opened ordered members => exact typed ordered members
      | sealed ordered =>
        unfold stageFields checkedNumericStage
        cases uniqueLoop [] (inputs.map (fun scalar => scalarKey scalar.words)) <;> rfl

theorem returned_checked_source_stage_derives_successful_projected_numeric_stage {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (previous : Option (WordTaggedObject Other))
    (inputs : List CanonicalScalar) (object : WordTaggedObject Other)
    (returned : stageFields previous inputs true (readerForPrevious (backend.readerGate child) (backend.lookup child) previous) = .ok (.ok object)) :
    checkedNumericStage backend child previous inputs = .ok (.ok (projectObjectPending object)) := by
  rw [← every_checked_source_stage_outcome_projects_to_checked_numeric_stage, returned]
  rfl

set_option pp.all true in
#check @projectObjectPending
#print axioms projectObjectPending
set_option pp.all true in
#check @previousPending
#print axioms previousPending
set_option pp.all true in
#check @readerForPrevious
#print axioms readerForPrevious
set_option pp.all true in
#check @checkedNumericStage
#print axioms checkedNumericStage
set_option pp.all true in
#check @projected_original_word_append_is_exact_numeric_pending_append
#print axioms projected_original_word_append_is_exact_numeric_pending_append
set_option pp.all true in
#check @numeric_inspection_recovers_after_original_field_write_and_projection
#print axioms numeric_inspection_recovers_after_original_field_write_and_projection
set_option pp.all true in
#check @every_checked_source_stage_outcome_projects_to_checked_numeric_stage
#print axioms every_checked_source_stage_outcome_projects_to_checked_numeric_stage
set_option pp.all true in
#check @returned_checked_source_stage_derives_successful_projected_numeric_stage
#print axioms returned_checked_source_stage_derives_successful_projected_numeric_stage
end ShielddSecurity.TransferCheckedWordStageRefinement01
