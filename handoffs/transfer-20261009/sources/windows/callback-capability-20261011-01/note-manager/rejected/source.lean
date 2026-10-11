import ShielddSecurity.TransferRawEffectsSource01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferNoteManagerSource01

open TransferStateDelta TransferRawStateProgram01

/-! Shared source recurrence for add_note_payload and
add_volume_accumulator_payload: SCT insertion precedes reading and appending
the current pending payload list and one object_put. Positions and source
observations are symbolic; full Rust payload/source codecs and SCT insertion
remain interfaces. A failed SCT callback can retain a changed cache. -/

structure Insertion (O E X : Type) where
  cache : Cache O E
  result : Except X Nat

structure Backend (O E X : Type) where
  sct : Delta O E → Nat → Bool → Insertion O E X
  pending : Delta O E → List (Nat × Nat × Bool)
  encode : List (Nat × Nat × Bool) → O

def insertPayload {O E X : Type} (backend : Backend O E X) (objectKey : Nat)
    (child : Delta O E) (payload : Nat) (capturedSource : Bool) : Outcome O E X :=
  let inserted := backend.sct child payload capturedSource
  match inserted.result with
  | .error error => ⟨inserted.cache, .error error⟩
  | .ok position =>
      let staged := {child with cache := inserted.cache}
      let queued := backend.pending staged ++ [(position, payload, capturedSource)]
      ⟨(putObject staged objectKey (some (backend.encode queued))).cache, .ok ()⟩

def installNotes {O E X : Type} (raw : TransferRawEffectsSource01.Backend O E X)
    (manager : Backend O E X) (objectKey : Nat) : TransferRawEffectsSource01.Backend O E X :=
  {raw with noteInsert := (fun child source payload => insertPayload manager objectKey child payload source)}

def installVolume {O E X : Type} (raw : TransferRawEffectsSource01.Backend O E X)
    (manager : Backend O E X) (objectKey payload : Nat) : TransferRawEffectsSource01.Backend O E X :=
  {raw with volumeInsert := (fun child source => insertPayload manager objectKey child payload source)}

theorem failed_sct_retains_its_cache_before_pending_append {O E X : Type}
    (backend : Backend O E X) (objectKey : Nat) (child : Delta O E) (payload : Nat)
    (capturedSource : Bool) (failureCache : Cache O E) (error : X)
    (failed : backend.sct child payload capturedSource = ⟨failureCache, .error error⟩) :
    insertPayload backend objectKey child payload capturedSource = ⟨failureCache, .error error⟩ := by
  simp only [insertPayload, failed]

theorem successful_sct_appends_to_post_sct_pending {O E X : Type}
    (backend : Backend O E X) (objectKey : Nat) (child : Delta O E) (payload position : Nat)
    (capturedSource : Bool) (sctCache : Cache O E)
    (passed : backend.sct child payload capturedSource = ⟨sctCache, .ok position⟩) :
    insertPayload backend objectKey child payload capturedSource =
      ⟨(putObject {child with cache := sctCache} objectKey
        (some (backend.encode (backend.pending {child with cache := sctCache} ++
          [(position, payload, capturedSource)])))).cache, .ok ()⟩ := by
  simp only [insertPayload, passed]

theorem success_recovers_actual_sct_position_and_cache {O E X : Type}
    (backend : Backend O E X) (objectKey : Nat) (child : Delta O E) (payload : Nat)
    (capturedSource : Bool) (updated : Cache O E)
    (success : insertPayload backend objectKey child payload capturedSource = ⟨updated, .ok ()⟩) :
    ∃ position,
      (backend.sct child payload capturedSource).result = .ok position ∧
      updated = (putObject {child with cache := (backend.sct child payload capturedSource).cache} objectKey
        (some (backend.encode (backend.pending {child with cache := (backend.sct child payload capturedSource).cache} ++
          [(position, payload, capturedSource)])))).cache := by
  cases observed : (backend.sct child payload capturedSource).result with
  | error error => simp [insertPayload, observed] at success
  | ok position =>
      have same : (putObject {child with cache := (backend.sct child payload capturedSource).cache} objectKey
          (some (backend.encode (backend.pending {child with cache := (backend.sct child payload capturedSource).cache} ++
            [(position, payload, capturedSource)])))).cache = updated := by
        simpa [insertPayload, observed] using success
      exact ⟨position, rfl, same.symm⟩

theorem successful_manager_frames_post_sct_components {O E X : Type}
    (backend : Backend O E X) (objectKey : Nat) (child : Delta O E) (payload : Nat)
    (capturedSource : Bool) (updated : Cache O E)
    (success : insertPayload backend objectKey child payload capturedSource = ⟨updated, .ok ()⟩) :
    updated.verifiable = (backend.sct child payload capturedSource).cache.verifiable ∧
      updated.nonverifiable = (backend.sct child payload capturedSource).cache.nonverifiable ∧
      updated.events = (backend.sct child payload capturedSource).cache.events ∧
      ∀ other, other ≠ objectKey → updated.objects other = (backend.sct child payload capturedSource).cache.objects other := by
  obtain ⟨_, _, same⟩ := success_recovers_actual_sct_position_and_cache backend objectKey child payload capturedSource updated success
  rw [same]
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro other different
  simp only [putObject, if_neg different]

theorem successful_manager_derives_visible_pending_object {O E X : Type}
    (backend : Backend O E X) (objectKey : Nat) (child : Delta O E) (payload : Nat)
    (capturedSource : Bool) (updated : Cache O E)
    (success : insertPayload backend objectKey child payload capturedSource = ⟨updated, .ok ()⟩) :
    ∃ position,
      (backend.sct child payload capturedSource).result = .ok position ∧
      (applyCache child.parent updated).objects objectKey =
        some (backend.encode (backend.pending {child with cache := (backend.sct child payload capturedSource).cache} ++
          [(position, payload, capturedSource)])) := by
  obtain ⟨position, observed, same⟩ := success_recovers_actual_sct_position_and_cache backend objectKey child payload capturedSource updated success
  refine ⟨position, observed, ?_⟩
  rw [same]
  simp only [putObject, applyCache, overlay, ite_true]

theorem note_callback_sct_failure_stops_semantic_event_and_suffix {O E X : Type}
    (raw : TransferRawEffectsSource01.Backend O E X) (manager : Backend O E X)
    (objectKey : Nat) (child : Delta O E) (output : Nat) (capturedSource : Bool)
    (rest : List Nat) (failureCache : Cache O E) (error : X)
    (failed : manager.sct child output capturedSource = ⟨failureCache, .error error⟩) :
    TransferRawEffectsSource01.notes (installNotes raw manager objectKey) capturedSource child (output :: rest) =
      ⟨failureCache, .error (.callback error)⟩ := by
  apply TransferRawEffectsSource01.failed_note_retains_cache_without_semantic_event
  exact failed_sct_retains_its_cache_before_pending_append manager objectKey child output capturedSource failureCache error failed

theorem note_callback_success_preserves_internal_events_then_adds_semantic_event {O E X : Type}
    (raw : TransferRawEffectsSource01.Backend O E X) (manager : Backend O E X)
    (objectKey : Nat) (child : Delta O E) (output position : Nat) (capturedSource : Bool)
    (sctCache : Cache O E)
    (passed : manager.sct child output capturedSource = ⟨sctCache, .ok position⟩) :
    (TransferRawEffectsSource01.notes (installNotes raw manager objectKey) capturedSource child [output]).cache.events =
      sctCache.events ++ [raw.noteEvent output] := by
  simp only [TransferRawEffectsSource01.notes, installNotes,
    successful_sct_appends_to_post_sct_pending manager objectKey child output position capturedSource sctCache passed,
    TransferRawEffectsSource01.liftCallback, next, TransferRawEffectsSource01.emit, putObject]

theorem ordinary_volume_payload_failure_retains_sct_failure_cache {O E X : Type}
    (raw : TransferRawEffectsSource01.Backend O E X) (manager : Backend O E X)
    (objectKey payload entryKey dayKey : Nat) (child : Delta O E) (capturedSource : Bool)
    (failureCache : Cache O E) (error : X)
    (source : raw.currentSource child = some capturedSource)
    (fresh : raw.volumePresent child = some false)
    (failed : manager.sct {child with cache := TransferRawEffectsSource01.putV
      (TransferRawEffectsSource01.putV child.cache entryKey [1]) dayKey [1]} payload capturedSource =
        ⟨failureCache, .error error⟩) :
    TransferRawEffectsSource01.volumeTail (installVolume raw manager objectKey payload) entryKey dayKey true child =
      ⟨failureCache, .error (.callback error)⟩ := by
  simp only [TransferRawEffectsSource01.volumeTail, installVolume, ↓reduceIte, source,
    TransferRawEffectsSource01.recordVolume, fresh, next,
    failed_sct_retains_its_cache_before_pending_append manager objectKey _ payload capturedSource failureCache error failed,
    TransferRawEffectsSource01.liftCallback]

set_option pp.all true in
#check @Insertion
#print axioms Insertion
set_option pp.all true in
#check @Backend
#print axioms Backend
set_option pp.all true in
#check @insertPayload
#print axioms insertPayload
set_option pp.all true in
#check @installNotes
#print axioms installNotes
set_option pp.all true in
#check @installVolume
#print axioms installVolume
set_option pp.all true in
#check @failed_sct_retains_its_cache_before_pending_append
#print axioms failed_sct_retains_its_cache_before_pending_append
set_option pp.all true in
#check @successful_sct_appends_to_post_sct_pending
#print axioms successful_sct_appends_to_post_sct_pending
set_option pp.all true in
#check @success_recovers_actual_sct_position_and_cache
#print axioms success_recovers_actual_sct_position_and_cache
set_option pp.all true in
#check @successful_manager_frames_post_sct_components
#print axioms successful_manager_frames_post_sct_components
set_option pp.all true in
#check @successful_manager_derives_visible_pending_object
#print axioms successful_manager_derives_visible_pending_object
set_option pp.all true in
#check @note_callback_sct_failure_stops_semantic_event_and_suffix
#print axioms note_callback_sct_failure_stops_semantic_event_and_suffix
set_option pp.all true in
#check @note_callback_success_preserves_internal_events_then_adds_semantic_event
#print axioms note_callback_success_preserves_internal_events_then_adds_semantic_event
set_option pp.all true in
#check @ordinary_volume_payload_failure_retains_sct_failure_cache
#print axioms ordinary_volume_payload_failure_retains_sct_failure_cache

end ShielddSecurity.TransferNoteManagerSource01
