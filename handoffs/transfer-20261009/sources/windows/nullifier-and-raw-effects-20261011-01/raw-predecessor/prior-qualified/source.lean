import ShielddSecurity.TransferNullifierBatchSource01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferRawEffectsSource01

open TransferStateDelta TransferRawStateProgram01

/-! Functional source order after exact capability rebinding. SCT insertion
callbacks may fail with a changed child cache and may emit internal events.
Semantic note-created events are emitted only after the corresponding callback
returns success. Volume freshness is re-read after note effects, and an ordinary
conflict preserves those raw effects until the enclosing delivery discards them.
Actual Rust ownership, callback/SCT semantics, encodings and authentication are
interfaces; this module adds no runtime or durable-publication credit. -/

inductive EffectError (X : Type) where
  | capability | source | batch (error : TransferNullifierBatchSource01.BatchError)
  | volumeRead | volumeSpent | callback (error : X)

structure Backend (O E X : Type) where
  nullifiers : TransferNullifierBatchSource01.Backend O E
  currentSource : Delta O E → Option Bool
  noteInsert : Delta O E → Nat → Outcome O E X
  volumePresent : Delta O E → Option Bool
  volumeInsert : Delta O E → Outcome O E X
  spentEvent : Nat → E
  noteEvent : Nat → E

def liftCallback {O E X : Type} (returned : Outcome O E X) : Outcome O E (EffectError X) :=
  ⟨returned.cache, match returned.result with
    | .error error => .error (.callback error)
    | .ok () => .ok ()⟩

def emit {O E : Type} (cache : Cache O E) (event : E) : Cache O E :=
  {cache with events := cache.events ++ [event]}

def emitSpends {O E : Type} (event : Nat → E) : Cache O E → List Nat → Cache O E
  | cache, [] => cache
  | cache, key :: rest => emitSpends event (emit cache (event key)) rest

def notes {O E X : Type} (backend : Backend O E X) :
    Delta O E → List Nat → Outcome O E (EffectError X)
  | child, [] => ⟨child.cache, .ok ()⟩
  | child, output :: rest =>
      next (liftCallback (backend.noteInsert child output)) (fun updated =>
        notes backend {child with cache := emit updated (backend.noteEvent output)} rest)

def putV {O E : Type} (cache : Cache O E) (key : Nat) (value : Bytes) : Cache O E :=
  {cache with verifiable := (fun other => if other = key then some (some value) else cache.verifiable other)}

def recordVolume {O E X : Type} (backend : Backend O E X) (entryKey dayKey : Nat)
    (child : Delta O E) : Outcome O E (EffectError X) :=
  match backend.volumePresent child with
  | none => ⟨child.cache, .error .volumeRead⟩
  | some true => ⟨child.cache, .error .volumeSpent⟩
  | some false => ⟨putV (putV child.cache entryKey [1]) dayKey [1], .ok ()⟩

def reshape {O E X : Type} (backend : Backend O E X) (wordMax capacity pendingKey : Nat)
    (child : Delta O E) (inputs outputs : List Nat) : Outcome O E (EffectError X) :=
  match backend.currentSource child with
  | none => ⟨child.cache, .error .source⟩
  | some sourceHasId =>
      let nul := TransferNullifierBatchSource01.executeNullify backend.nullifiers wordMax capacity pendingKey sourceHasId child inputs
      match nul.result with
      | .error error => ⟨nul.cache, .error (.batch error)⟩
      | .ok () => notes backend {child with cache := emitSpends backend.spentEvent nul.cache inputs} outputs

def volumeTail {O E X : Type} (backend : Backend O E X) (entryKey dayKey : Nat)
    (ordinary : Bool) (child : Delta O E) : Outcome O E (EffectError X) :=
  if ordinary then
    match backend.currentSource child with
    | none => ⟨child.cache, .error .source⟩
    | some _ => next (recordVolume backend entryKey dayKey child)
        (fun updated => liftCallback (backend.volumeInsert {child with cache := updated}))
  else ⟨child.cache, .ok ()⟩

def executeTransfer {O E X : Type} (backend : Backend O E X)
    (wordMax capacity pendingKey entryKey dayKey : Nat) (exactMatched ordinary : Bool)
    (child : Delta O E) (inputs outputs : List Nat) : Outcome O E (EffectError X) :=
  if exactMatched then
    next (reshape backend wordMax capacity pendingKey child inputs outputs)
      (fun updated => volumeTail backend entryKey dayKey ordinary {child with cache := updated})
  else ⟨child.cache, .error .capability⟩

theorem emitSpends_exact {O E : Type} (event : Nat → E) (cache : Cache O E) (keys : List Nat) :
    emitSpends event cache keys = {cache with events := cache.events ++ keys.map event} := by
  induction keys generalizing cache with
  | nil => simp [emitSpends]
  | cons key rest ih =>
      rw [emitSpends, ih]
      simp [emit, List.append_assoc]

theorem failed_note_retains_cache_without_semantic_event {O E X : Type}
    (backend : Backend O E X) (child : Delta O E) (output : Nat) (rest : List Nat)
    (failureCache : Cache O E) (error : X)
    (failed : backend.noteInsert child output = ⟨failureCache, .error error⟩) :
    notes backend child (output :: rest) = ⟨failureCache, .error (.callback error)⟩ := by
  simp only [notes, failed, liftCallback, next]

theorem successful_note_emits_then_recurses {O E X : Type}
    (backend : Backend O E X) (child : Delta O E) (output : Nat) (rest : List Nat)
    (updated : Cache O E) (passed : backend.noteInsert child output = ⟨updated, .ok ()⟩) :
    notes backend child (output :: rest) =
      notes backend {child with cache := emit updated (backend.noteEvent output)} rest := by
  simp only [notes, passed, liftCallback, next]

theorem missing_reshape_source_precedes_even_empty_input {O E X : Type}
    (backend : Backend O E X) (wordMax capacity pendingKey : Nat) (child : Delta O E)
    (inputs outputs : List Nat) (missing : backend.currentSource child = none) :
    reshape backend wordMax capacity pendingKey child inputs outputs =
      ⟨child.cache, .error .source⟩ := by
  simp only [reshape, missing]

theorem successful_nullify_emits_all_spends_before_notes {O E X : Type}
    (backend : Backend O E X) (wordMax capacity pendingKey : Nat) (child : Delta O E)
    (inputs outputs : List Nat) (sourceHasId : Bool) (updated : Cache O E)
    (source : backend.currentSource child = some sourceHasId)
    (passed : TransferNullifierBatchSource01.executeNullify backend.nullifiers wordMax capacity pendingKey sourceHasId child inputs =
      ⟨updated, .ok ()⟩) :
    reshape backend wordMax capacity pendingKey child inputs outputs =
      notes backend {child with cache := {updated with events := updated.events ++ inputs.map backend.spentEvent}} outputs := by
  simp only [reshape, source, passed, emitSpends_exact]

theorem volume_conflict_is_readonly {O E X : Type} (backend : Backend O E X)
    (entryKey dayKey : Nat) (child : Delta O E) (spent : backend.volumePresent child = some true) :
    recordVolume backend entryKey dayKey child = ⟨child.cache, .error .volumeSpent⟩ := by
  simp only [recordVolume, spent]

theorem successful_volume_derives_read_and_two_writes {O E X : Type}
    (backend : Backend O E X) (entryKey dayKey : Nat) (child : Delta O E) (updated : Cache O E)
    (success : recordVolume backend entryKey dayKey child = ⟨updated, .ok ()⟩) :
    backend.volumePresent child = some false ∧ updated = putV (putV child.cache entryKey [1]) dayKey [1] := by
  cases observed : backend.volumePresent child with
  | none => simp [recordVolume, observed] at success
  | some spent =>
    cases spent with
    | true => simp [recordVolume, observed] at success
    | false =>
      have same : putV (putV child.cache entryKey [1]) dayKey [1] = updated := by
        simpa [recordVolume, observed] using success
      exact ⟨rfl, same.symm⟩

theorem successful_volume_values_and_frame {O E X : Type} (backend : Backend O E X)
    (entryKey dayKey : Nat) (child : Delta O E) (updated : Cache O E)
    (different : entryKey ≠ dayKey)
    (success : recordVolume backend entryKey dayKey child = ⟨updated, .ok ()⟩) :
    updated.verifiable entryKey = some (some [1]) ∧ updated.verifiable dayKey = some (some [1]) ∧
      updated.nonverifiable = child.cache.nonverifiable ∧ updated.objects = child.cache.objects ∧
      updated.events = child.cache.events ∧
      ∀ other, other ≠ entryKey → other ≠ dayKey → updated.verifiable other = child.cache.verifiable other := by
  obtain ⟨_, same⟩ := successful_volume_derives_read_and_two_writes backend entryKey dayKey child updated success
  rw [same]
  refine ⟨?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [putV, if_neg different, ite_true]
  · simp only [putV, ite_true]
  · intro other notEntry notDay
    simp only [putV, if_neg notEntry, if_neg notDay]

theorem capability_mismatch_precedes_effects {O E X : Type} (backend : Backend O E X)
    (wordMax capacity pendingKey entryKey dayKey : Nat) (ordinary : Bool)
    (child : Delta O E) (inputs outputs : List Nat) :
    executeTransfer backend wordMax capacity pendingKey entryKey dayKey false ordinary child inputs outputs =
      ⟨child.cache, .error .capability⟩ := rfl

theorem regulated_skips_volume_tail {O E X : Type} (backend : Backend O E X)
    (entryKey dayKey : Nat) (child : Delta O E) :
    volumeTail backend entryKey dayKey false child = ⟨child.cache, .ok ()⟩ := rfl

theorem ordinary_conflict_suppresses_payload {O E X : Type} (backend : Backend O E X)
    (entryKey dayKey : Nat) (child : Delta O E) (sourceHasId : Bool)
    (source : backend.currentSource child = some sourceHasId)
    (spent : backend.volumePresent child = some true) :
    volumeTail backend entryKey dayKey true child = ⟨child.cache, .error .volumeSpent⟩ := by
  simp only [volumeTail, ↓reduceIte, source, volume_conflict_is_readonly backend entryKey dayKey child spent, next]

theorem actual_late_volume_conflict_keeps_earlier_raw_cache {O E X : Type}
    (backend : Backend O E X) (wordMax capacity pendingKey entryKey dayKey : Nat)
    (child : Delta O E) (inputs outputs : List Nat) (middle : Cache O E) (sourceHasId : Bool)
    (reshaped : reshape backend wordMax capacity pendingKey child inputs outputs = ⟨middle, .ok ()⟩)
    (source : backend.currentSource {child with cache := middle} = some sourceHasId)
    (spent : backend.volumePresent {child with cache := middle} = some true) :
    executeTransfer backend wordMax capacity pendingKey entryKey dayKey true true child inputs outputs =
      ⟨middle, .error .volumeSpent⟩ := by
  simp only [executeTransfer, ↓reduceIte, reshaped, next]
  exact ordinary_conflict_suppresses_payload backend entryKey dayKey _ sourceHasId source spent

set_option pp.all true in
#check @EffectError
#print axioms EffectError
set_option pp.all true in
#check @Backend
#print axioms Backend
set_option pp.all true in
#check @liftCallback
#print axioms liftCallback
set_option pp.all true in
#check @emit
#print axioms emit
set_option pp.all true in
#check @emitSpends
#print axioms emitSpends
set_option pp.all true in
#check @notes
#print axioms notes
set_option pp.all true in
#check @putV
#print axioms putV
set_option pp.all true in
#check @recordVolume
#print axioms recordVolume
set_option pp.all true in
#check @reshape
#print axioms reshape
set_option pp.all true in
#check @volumeTail
#print axioms volumeTail
set_option pp.all true in
#check @executeTransfer
#print axioms executeTransfer
set_option pp.all true in
#check @emitSpends_exact
#print axioms emitSpends_exact
set_option pp.all true in
#check @failed_note_retains_cache_without_semantic_event
#print axioms failed_note_retains_cache_without_semantic_event
set_option pp.all true in
#check @successful_note_emits_then_recurses
#print axioms successful_note_emits_then_recurses
set_option pp.all true in
#check @missing_reshape_source_precedes_even_empty_input
#print axioms missing_reshape_source_precedes_even_empty_input
set_option pp.all true in
#check @successful_nullify_emits_all_spends_before_notes
#print axioms successful_nullify_emits_all_spends_before_notes
set_option pp.all true in
#check @volume_conflict_is_readonly
#print axioms volume_conflict_is_readonly
set_option pp.all true in
#check @successful_volume_derives_read_and_two_writes
#print axioms successful_volume_derives_read_and_two_writes
set_option pp.all true in
#check @successful_volume_values_and_frame
#print axioms successful_volume_values_and_frame
set_option pp.all true in
#check @capability_mismatch_precedes_effects
#print axioms capability_mismatch_precedes_effects
set_option pp.all true in
#check @regulated_skips_volume_tail
#print axioms regulated_skips_volume_tail
set_option pp.all true in
#check @ordinary_conflict_suppresses_payload
#print axioms ordinary_conflict_suppresses_payload
set_option pp.all true in
#check @actual_late_volume_conflict_keeps_earlier_raw_cache
#print axioms actual_late_volume_conflict_keeps_earlier_raw_cache

end ShielddSecurity.TransferRawEffectsSource01
