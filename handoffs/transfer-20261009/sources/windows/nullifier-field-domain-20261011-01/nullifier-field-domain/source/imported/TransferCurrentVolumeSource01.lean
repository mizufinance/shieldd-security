import ShielddSecurity.TransferRawSourceFrames01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferCurrentVolumeSource01

open TransferStateDelta TransferRawStateProgram01

/-! The volume existence check reads current child-overlay presence of any
value at the projected day/nullifier key. Read failure is kept separate from
absence. Source-derived note V/NV framing makes an existing entry persist until
the ordinary recheck, even when note reshaping may return an error. Under the
scoped immutable/successful-load model, no successful reshape or desired spent
flag is a premise of existing-volume refusal. Actual Rust get_raw/store/key
correspondence and all inherited tree/clone/proof interfaces remain open. -/

def readVolume {O E : Type} (available : Delta O E → Bool) (entryKey : Nat)
    (child : Delta O E) : Option Bool :=
  if available child then some ((applyCache child.parent child.cache).verifiable entryKey).isSome else none

def withVolumeRead {O E X : Type} (raw : TransferRawEffectsSource01.Backend O E X)
    (available : Delta O E → Bool) (entryKey : Nat) : TransferRawEffectsSource01.Backend O E X :=
  {raw with volumePresent := readVolume available entryKey}

def executeOrdinary {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (wordMax capacity treeKey pendingKey nullifierKey entryKey dayKey : Nat)
    (exactMatched : Bool) (child : Delta O E) (inputs outputs : List Nat) :
    Outcome O E (TransferRawEffectsSource01.EffectError (TransferSctInsertionSource01.Error X)) :=
  TransferRawEffectsSource01.executeTransfer
    (TransferRawSourceFrames01.installNotes (withVolumeRead raw available entryKey) manager sct treeKey pendingKey)
    wordMax capacity nullifierKey entryKey dayKey exactMatched true child inputs outputs

theorem present_entry_reads_spent_when_available {O E : Type}
    (available : Delta O E → Bool) (entryKey : Nat) (child : Delta O E) (bytes : Bytes)
    (readable : available child = true)
    (present : (applyCache child.parent child.cache).verifiable entryKey = some bytes) :
    readVolume available entryKey child = some true := by
  simp [readVolume, readable, present]

theorem volume_tail_existing_entry_refuses {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (treeKey pendingKey entryKey dayKey : Nat) (child : Delta O E) (bytes : Bytes)
    (present : (applyCache child.parent child.cache).verifiable entryKey = some bytes) :
    asCache (TransferRawEffectsSource01.volumeTail
      (TransferRawSourceFrames01.installNotes (withVolumeRead raw available entryKey) manager sct treeKey pendingKey)
      entryKey dayKey true child) = none := by
  cases source : raw.currentSource child with
  | none =>
    simp [TransferRawEffectsSource01.volumeTail, TransferRawSourceFrames01.installNotes,
      TransferNoteManagerSource01.installNotes, withVolumeRead, source, asCache]
  | some sourceHasId =>
    cases readable : available child with
    | false =>
      simp [TransferRawEffectsSource01.volumeTail, TransferRawSourceFrames01.installNotes,
        TransferNoteManagerSource01.installNotes, withVolumeRead, source,
        TransferRawEffectsSource01.recordVolume, readVolume, readable, next, asCache]
    | true =>
      simp [TransferRawEffectsSource01.volumeTail, TransferRawSourceFrames01.installNotes,
        TransferNoteManagerSource01.installNotes, withVolumeRead, source,
        TransferRawEffectsSource01.recordVolume, readVolume, readable, present, next, asCache]

theorem existing_current_volume_excludes_success {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (wordMax capacity treeKey pendingKey nullifierKey entryKey dayKey : Nat)
    (exactMatched : Bool) (child : Delta O E) (inputs outputs : List Nat) (bytes : Bytes)
    (present : (applyCache child.parent child.cache).verifiable entryKey = some bytes) :
    asCache (executeOrdinary raw manager sct available wordMax capacity treeKey pendingKey nullifierKey
      entryKey dayKey exactMatched child inputs outputs) = none := by
  cases exactMatched with
  | false => rfl
  | true =>
    have frames := TransferRawSourceFrames01.reshape_preserves_input_write_domains
      (withVolumeRead raw available entryKey) manager sct wordMax capacity treeKey pendingKey nullifierKey child inputs outputs
    cases result : (TransferRawEffectsSource01.reshape
      (TransferRawSourceFrames01.installNotes (withVolumeRead raw available entryKey) manager sct treeKey pendingKey)
      wordMax capacity nullifierKey child inputs outputs).result with
    | error error =>
      simp only [executeOrdinary, TransferRawEffectsSource01.executeTransfer, ↓reduceIte, result, next, asCache]
    | ok returnedUnit =>
      cases returnedUnit
      have currentPresent : (applyCache child.parent (TransferRawEffectsSource01.reshape
          (TransferRawSourceFrames01.installNotes (withVolumeRead raw available entryKey) manager sct treeKey pendingKey)
          wordMax capacity nullifierKey child inputs outputs).cache).verifiable entryKey = some bytes := by
        change overlay child.parent.verifiable _ entryKey = some bytes
        rw [frames.1]
        exact present
      simp only [executeOrdinary, TransferRawEffectsSource01.executeTransfer, ↓reduceIte, result, next]
      exact volume_tail_existing_entry_refuses raw manager sct available treeKey pendingKey entryKey dayKey
        {child with cache := (TransferRawEffectsSource01.reshape
          (TransferRawSourceFrames01.installNotes (withVolumeRead raw available entryKey) manager sct treeKey pendingKey)
          wordMax capacity nullifierKey child inputs outputs).cache} bytes currentPresent

def deliveryApi {O E X Tree T : Type} (api : Api O E T)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (wordMax capacity treeKey pendingKey nullifierKey entryKey dayKey : Nat)
    (exactMatched : Bool) (inputs outputs : List Nat) : Api O E T :=
  {api with execute := (fun child => asCache (executeOrdinary raw manager sct available
    wordMax capacity treeKey pendingKey nullifierKey entryKey dayKey exactMatched child inputs outputs))}

theorem existing_parent_volume_rejects_delivery {O E X Tree T : Type} (api : Api O E T)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (wordMax capacity treeKey pendingKey nullifierKey entryKey dayKey : Nat)
    (exactMatched registryMatches exclusive : Bool) (mode : IndexMode) (transaction : T)
    (inputs outputs : List Nat) (parent : State O) (queued : List T) (bytes : Bytes)
    (present : parent.verifiable entryKey = some bytes) :
    run (deliveryApi api raw manager sct available wordMax capacity treeKey pendingKey nullifierKey
      entryKey dayKey exactMatched inputs outputs) registryMatches exclusive mode transaction parent queued = none := by
  have currentPresent : (applyCache parent (empty (O := O) (E := E))).verifiable entryKey = some bytes := by
    rw [apply_empty]
    exact present
  have rejected := existing_current_volume_excludes_success raw manager sct available
    wordMax capacity treeKey pendingKey nullifierKey entryKey dayKey exactMatched ⟨parent, empty⟩ inputs outputs bytes currentPresent
  cases registryMatches with
  | false => rfl
  | true =>
    cases exclusive with
    | false => rfl
    | true => simp only [run, begin, deliveryApi, ↓reduceIte, Option.bind_some, rejected, Option.bind_none]

theorem existing_parent_volume_preserves_parent_and_queue {O E X Tree T : Type} (api : Api O E T)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (wordMax capacity treeKey pendingKey nullifierKey entryKey dayKey : Nat)
    (exactMatched registryMatches exclusive : Bool) (mode : IndexMode) (transaction : T)
    (inputs outputs : List Nat) (parent : State O) (queued : List T) (bytes : Bytes)
    (present : parent.verifiable entryKey = some bytes) :
    finish parent queued (run (deliveryApi api raw manager sct available wordMax capacity treeKey pendingKey nullifierKey
      entryKey dayKey exactMatched inputs outputs) registryMatches exclusive mode transaction parent queued) = (parent, queued) := by
  exact delivery_failure_preserves_parent_and_queue _ _ _ _ _ _ _
    (existing_parent_volume_rejects_delivery api raw manager sct available wordMax capacity treeKey pendingKey
      nullifierKey entryKey dayKey exactMatched registryMatches exclusive mode transaction inputs outputs parent queued bytes present)


set_option pp.all true in
#check @readVolume
#print axioms readVolume
set_option pp.all true in
#check @withVolumeRead
#print axioms withVolumeRead
set_option pp.all true in
#check @executeOrdinary
#print axioms executeOrdinary
set_option pp.all true in
#check @present_entry_reads_spent_when_available
#print axioms present_entry_reads_spent_when_available
set_option pp.all true in
#check @volume_tail_existing_entry_refuses
#print axioms volume_tail_existing_entry_refuses
set_option pp.all true in
#check @existing_current_volume_excludes_success
#print axioms existing_current_volume_excludes_success
set_option pp.all true in
#check @deliveryApi
#print axioms deliveryApi
set_option pp.all true in
#check @existing_parent_volume_rejects_delivery
#print axioms existing_parent_volume_rejects_delivery
set_option pp.all true in
#check @existing_parent_volume_preserves_parent_and_queue
#print axioms existing_parent_volume_preserves_parent_and_queue

end ShielddSecurity.TransferCurrentVolumeSource01
