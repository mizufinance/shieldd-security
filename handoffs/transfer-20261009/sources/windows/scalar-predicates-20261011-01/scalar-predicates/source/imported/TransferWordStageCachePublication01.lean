import ShielddSecurity.TransferCheckedWordStageRefinement01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWordStageCachePublication01
attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey
open TransferStateDelta (View Writes overlay Delta)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferWordStageOrder01 (stageFields)
open TransferWordStageAdmission01 (returned_whole_stage_derives_prior_typed_branch_all_checks_and_exact_original_field_append)
open TransferCheckedWordStageRefinement01 (readerForPrevious checkedNumericStage projectObjectPending)
open TransferNullifierBatchSource01 (Backend BatchError uniqueLoop)
open TransferWordObjectRead01 (checkedObject)
open TransferScalarLittleEndianBytes01 (scalarKey)
/-! A returned checked source stage writes one selected live functional cache
slot, retains original fields, and derives the next checked getter and all
other-key frames. The modeled durable reader captures the actual selected
prior slot, not a caller expected pending value. No desired cache, successful
getter, codec inverse, type-domain or field-frame premise is supplied. Native
live-cache/Any/Clone/map/reader/Scalar/usize/compiler/ownership/async/full trace
bindings remain OPEN. Source semantics only, no native/control/certification. -/

def stageAtKey {O E Other : Type} (backend : Backend O E) (child : Delta O E)
    (parent : View (WordTaggedObject Other)) (writes : Writes (WordTaggedObject Other))
    (key : Nat) (inputs : List CanonicalScalar) : Except Unit (Except BatchError (Writes (WordTaggedObject Other))) :=
  (stageFields ((overlay parent writes) key) inputs true
    (readerForPrevious (backend.readerGate child) (backend.lookup child) ((overlay parent writes) key))).map
      (fun result => result.map (fun object other => if other = key then some (some object) else writes other))

theorem returned_stage_at_key_derives_exact_returned_object_and_one_cache_write {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other))
    (writes next : Writes (WordTaggedObject Other)) (key : Nat) (inputs : List CanonicalScalar)
    (returned : stageAtKey backend child parent writes key inputs = .ok (.ok next)) :
    ∃ object : WordTaggedObject Other,
      stageFields ((overlay parent writes) key) inputs true
        (readerForPrevious (backend.readerGate child) (backend.lookup child) ((overlay parent writes) key)) = .ok (.ok object) ∧
      next = (fun other => if other = key then some (some object) else writes other) := by
  unfold stageAtKey at returned
  simp only [Except.map] at returned
  cases staged : stageFields ((overlay parent writes) key) inputs true
      (readerForPrevious (backend.readerGate child) (backend.lookup child) ((overlay parent writes) key)) with
  | error panic => rw [staged] at returned; cases returned
  | ok result =>
    rw [staged] at returned
    cases result with
    | error refusal => cases returned
    | ok object =>
      have exactCache := Except.ok.inj (Except.ok.inj returned)
      exact ⟨object, rfl, exactCache.symm⟩

theorem returned_cached_stage_derives_original_fields_checked_getter_and_all_other_key_frames {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other))
    (writes next : Writes (WordTaggedObject Other)) (key : Nat) (inputs : List CanonicalScalar)
    (returned : stageAtKey backend child parent writes key inputs = .ok (.ok next)) :
    uniqueLoop [] (inputs.map (fun scalar => scalarKey scalar.words)) = true ∧
      ∃ ordered members : List CanonicalScalar,
        ordered.length + inputs.length ≤ TransferNullifierConsensusLimits01.blockCapacity ∧
        next key = some (some (.inl (.opened (ordered ++ inputs) (members ++ inputs)))) ∧
        checkedObject ((overlay parent next) key) = .ok (some (.opened (ordered ++ inputs) (members ++ inputs))) ∧
        ∀ other, other ≠ key → next other = writes other ∧ (overlay parent next) other = (overlay parent writes) other := by
  obtain ⟨object, staged, cached⟩ := returned_stage_at_key_derives_exact_returned_object_and_one_cache_write
    backend child parent writes next key inputs returned
  obtain ⟨unique, ordered, members, _, capacity, _, _, written⟩ :=
    returned_whole_stage_derives_prior_typed_branch_all_checks_and_exact_original_field_append
      ((overlay parent writes) key) inputs true
      (readerForPrevious (backend.readerGate child) (backend.lookup child) ((overlay parent writes) key)) object staged
  have atKey : next key = some (some (.inl (.opened (ordered ++ inputs) (members ++ inputs)))) := by
    rw [cached, written]
    exact if_pos rfl
  have checked : checkedObject ((overlay parent next) key) = .ok (some (.opened (ordered ++ inputs) (members ++ inputs))) := by
    simp only [overlay, atKey, checkedObject]
  refine ⟨unique, ordered, members, capacity, atKey, checked, ?_⟩
  intro other different
  have framed : next other = writes other := by
    rw [cached]
    exact if_neg different
  refine ⟨framed, ?_⟩
  simp only [overlay, framed]

theorem returned_cached_source_stage_derives_checked_numeric_stage_at_actual_previous_slot {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other))
    (writes next : Writes (WordTaggedObject Other)) (key : Nat) (inputs : List CanonicalScalar)
    (returned : stageAtKey backend child parent writes key inputs = .ok (.ok next)) :
    ∃ object : WordTaggedObject Other,
      (overlay parent next) key = some object ∧
      checkedNumericStage backend child ((overlay parent writes) key) inputs = .ok (.ok (projectObjectPending object)) := by
  obtain ⟨object, staged, cached⟩ := returned_stage_at_key_derives_exact_returned_object_and_one_cache_write
    backend child parent writes next key inputs returned
  have atKey : next key = some (some object) := by
    rw [cached]
    exact if_pos rfl
  refine ⟨object, ?_, TransferCheckedWordStageRefinement01.returned_checked_source_stage_derives_successful_projected_numeric_stage
    backend child ((overlay parent writes) key) inputs object staged⟩
  simp only [overlay, atKey]

set_option pp.all true in
#check @stageAtKey
#print axioms stageAtKey
set_option pp.all true in
#check @returned_stage_at_key_derives_exact_returned_object_and_one_cache_write
#print axioms returned_stage_at_key_derives_exact_returned_object_and_one_cache_write
set_option pp.all true in
#check @returned_cached_stage_derives_original_fields_checked_getter_and_all_other_key_frames
#print axioms returned_cached_stage_derives_original_fields_checked_getter_and_all_other_key_frames
set_option pp.all true in
#check @returned_cached_source_stage_derives_checked_numeric_stage_at_actual_previous_slot
#print axioms returned_cached_source_stage_derives_checked_numeric_stage_at_actual_previous_slot
end ShielddSecurity.TransferWordStageCachePublication01
