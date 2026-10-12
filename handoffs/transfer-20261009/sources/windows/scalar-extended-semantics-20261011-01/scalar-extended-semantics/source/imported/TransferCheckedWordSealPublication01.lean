import ShielddSecurity.TransferCheckedWordSeal01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCheckedWordSealPublication01
open TransferStateDelta (View Writes overlay Delta)
open TransferWordObjectCodec01 (WordTaggedObject)
open TransferCanonicalWordEquality01 (CanonicalScalar)
open TransferCheckedWordSeal01 (sealFields sealAtKey)
open TransferWordSctPendingRead01 (sourceOrdered sourceIsSealed sourceEnsureSealed)
open TransferWordStageCachePublication01 (stageAtKey)
open TransferNullifierBatchSource01 (Backend)
/-! Returned checked source seal publishes the actual selected functional
cache object and derives all three subsequent SCT observations and other-key
frames. Joining a returned stage and seal derives original ordered fields and
capacity without supplied getter/domain/inverse/expected-cache premises.
Native cache/Any/Clone/imbl/Scalar/reader/compiler/full trace remains OPEN. -/

theorem returned_seal_at_key_derives_exact_one_slot_original_field_write {Other : Type}
    (parent : View (WordTaggedObject Other)) (writes next : Writes (WordTaggedObject Other)) (key : Nat)
    (returned : sealAtKey parent writes key = .ok (.ok next)) :
    ∃ ordered : List CanonicalScalar,
      next = (fun other => if other = key then some (some (.inl (.sealed ordered))) else writes other) := by
  unfold sealAtKey at returned
  simp only [Except.map] at returned
  cases sealedResult : sealFields ((overlay parent writes) key) with
  | error panic => rw [sealedResult] at returned; cases returned
  | ok result =>
    rw [sealedResult] at returned
    cases result with
    | error refusal => cases returned
    | ok object =>
      obtain ⟨ordered, _, same⟩ :=
        TransferCheckedWordSeal01.returned_seal_derives_actual_prior_absent_or_open_and_exact_original_fields
          ((overlay parent writes) key) object sealedResult
      have cache := (Except.ok.inj (Except.ok.inj returned)).symm
      rw [same] at cache
      exact ⟨ordered, cache⟩

theorem returned_cache_seal_derives_actual_selected_object_all_sct_getters_and_other_key_frames {Other : Type}
    (parent : View (WordTaggedObject Other)) (writes next : Writes (WordTaggedObject Other)) (key : Nat)
    (returned : sealAtKey parent writes key = .ok (.ok next)) :
    ∃ ordered : List CanonicalScalar,
      (overlay parent next) key = some (.inl (.sealed ordered)) ∧
      sourceOrdered ((overlay parent next) key) = .ok ordered ∧
      sourceIsSealed ((overlay parent next) key) = .ok true ∧
      sourceEnsureSealed ((overlay parent next) key) = .ok (.ok ()) ∧
      ∀ other, other ≠ key → next other = writes other ∧ (overlay parent next) other = (overlay parent writes) other := by
  obtain ⟨ordered, cached⟩ := returned_seal_at_key_derives_exact_one_slot_original_field_write parent writes next key returned
  have atKey : next key = some (some (.inl (.sealed ordered))) := by
    rw [cached]
    exact if_pos rfl
  have selected : (overlay parent next) key = some (.inl (.sealed ordered)) := by
    simp only [overlay, atKey]
  refine ⟨ordered, selected, ?_, ?_, ?_, ?_⟩
  · rw [selected]; rfl
  · rw [selected]; rfl
  · rw [selected]; rfl
  · intro other different
    have framed : next other = writes other := by
      rw [cached]
      exact if_neg different
    refine ⟨framed, ?_⟩
    simp only [overlay, framed]

theorem returned_stage_then_seal_derives_original_fields_capacity_and_actual_readback {O E Other : Type}
    (backend : Backend O E) (child : Delta O E) (parent : View (WordTaggedObject Other))
    (writes staged final : Writes (WordTaggedObject Other)) (key : Nat) (inputs : List CanonicalScalar)
    (stagedReturned : stageAtKey backend child parent writes key inputs = .ok (.ok staged))
    (sealedReturned : sealAtKey parent staged key = .ok (.ok final)) :
    ∃ ordered : List CanonicalScalar,
      ordered.length + inputs.length ≤ TransferNullifierConsensusLimits01.blockCapacity ∧
      (overlay parent final) key = some (.inl (.sealed (ordered ++ inputs))) ∧
      sourceOrdered ((overlay parent final) key) = .ok (ordered ++ inputs) ∧
      sourceIsSealed ((overlay parent final) key) = .ok true ∧
      sourceEnsureSealed ((overlay parent final) key) = .ok (.ok ()) := by
  obtain ⟨_, ordered, members, capacity, atKey, _, _⟩ :=
    TransferWordStageCachePublication01.returned_cached_stage_derives_original_fields_checked_getter_and_all_other_key_frames
      backend child parent writes staged key inputs stagedReturned
  have selected : (overlay parent staged) key = some (.inl (.opened (ordered ++ inputs) (members ++ inputs))) := by
    simp only [overlay, atKey]
  simp only [sealAtKey, selected] at sealedReturned
  have cached : final = (fun other => if other = key then
      some (some (.inl (.sealed (ordered ++ inputs)) : WordTaggedObject Other)) else staged other) :=
    (Except.ok.inj (Except.ok.inj sealedReturned)).symm
  have finalKey : final key = some (some (.inl (.sealed (ordered ++ inputs)))) := by
    rw [cached]
    exact if_pos rfl
  have actual : (overlay parent final) key = some (.inl (.sealed (ordered ++ inputs))) := by
    simp only [overlay, finalKey]
  refine ⟨ordered, capacity, actual, ?_, ?_, ?_⟩
  · rw [actual]; rfl
  · rw [actual]; rfl
  · rw [actual]; rfl

set_option pp.all true in
#check @returned_seal_at_key_derives_exact_one_slot_original_field_write
#print axioms returned_seal_at_key_derives_exact_one_slot_original_field_write
set_option pp.all true in
#check @returned_cache_seal_derives_actual_selected_object_all_sct_getters_and_other_key_frames
#print axioms returned_cache_seal_derives_actual_selected_object_all_sct_getters_and_other_key_frames
set_option pp.all true in
#check @returned_stage_then_seal_derives_original_fields_capacity_and_actual_readback
#print axioms returned_stage_then_seal_derives_original_fields_capacity_and_actual_readback
end ShielddSecurity.TransferCheckedWordSealPublication01
