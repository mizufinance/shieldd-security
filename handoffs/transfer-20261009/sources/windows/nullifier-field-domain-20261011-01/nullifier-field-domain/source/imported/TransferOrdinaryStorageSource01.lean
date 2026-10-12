import ShielddSecurity.TransferCurrentVolumeSource01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferOrdinaryStorageSource01

open TransferStateDelta TransferRawStateProgram01

/-! Both payload callbacks install the successfully loaded immutable SCT
program and pending-object append. This derives V/NV framing even on returned
errors and ordinary marker writes from current overlay reads. Rust ownership,
loader panic, tree semantics, codecs, authenticated readers and durability are
separate interfaces. Earlier objects/events may remain changed on errors. -/

def installVolume {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (treeKey pendingKey payload : Nat) :
    TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X) :=
  TransferNoteManagerSource01.installVolume raw
    (TransferSctInsertionSource01.installSct manager sct treeKey) pendingKey payload

def installBoth {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (treeKey notesKey volumeKey payload entryKey : Nat) :
    TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X) :=
  TransferRawSourceFrames01.installNotes
    (installVolume (TransferCurrentVolumeSource01.withVolumeRead raw available entryKey)
      volume sct treeKey volumeKey payload) notes sct treeKey notesKey

def execute {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (exactMatched : Bool) (child : Delta O E) (inputs outputs : List Nat) :
    Outcome O E (TransferRawEffectsSource01.EffectError (TransferSctInsertionSource01.Error X)) :=
  TransferRawEffectsSource01.executeTransfer
    (installBoth raw notes volume sct available treeKey notesKey volumeKey payload entryKey)
    wordMax capacity nullifierKey entryKey dayKey exactMatched true child inputs outputs

theorem volume_payload_preserves_input_write_domains {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (treeKey pendingKey payload : Nat)
    (child : Delta O E) (source : Bool) :
    ((installVolume raw manager sct treeKey pendingKey payload).volumeInsert child source).cache.verifiable = child.cache.verifiable ∧
      ((installVolume raw manager sct treeKey pendingKey payload).volumeInsert child source).cache.nonverifiable = child.cache.nonverifiable := by
  exact TransferRawSourceFrames01.manager_preserves_input_write_domains manager sct treeKey pendingKey child payload source

theorem tail_ignores_note_callback {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (treeKey pendingKey entryKey dayKey : Nat)
    (child : Delta O E) :
    TransferRawEffectsSource01.volumeTail
      (TransferRawSourceFrames01.installNotes raw manager sct treeKey pendingKey) entryKey dayKey true child =
      TransferRawEffectsSource01.volumeTail raw entryKey dayKey true child := rfl

theorem tail_installBoth {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (treeKey notesKey volumeKey payload entryKey dayKey : Nat) (child : Delta O E) :
    TransferRawEffectsSource01.volumeTail
      (installBoth raw notes volume sct available treeKey notesKey volumeKey payload entryKey) entryKey dayKey true child =
      TransferRawEffectsSource01.volumeTail
        (installVolume (TransferCurrentVolumeSource01.withVolumeRead raw available entryKey)
          volume sct treeKey volumeKey payload) entryKey dayKey true child := rfl

theorem fresh_tail_retains_two_writes_on_any_return {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (treeKey pendingKey payload entryKey dayKey : Nat) (child : Delta O E) (source : Bool)
    (captured : raw.currentSource child = some source)
    (fresh : TransferCurrentVolumeSource01.readVolume available entryKey child = some false) :
    (TransferRawEffectsSource01.volumeTail
      (installVolume (TransferCurrentVolumeSource01.withVolumeRead raw available entryKey)
        manager sct treeKey pendingKey payload) entryKey dayKey true child).cache.verifiable =
        (TransferRawEffectsSource01.putV (TransferRawEffectsSource01.putV child.cache entryKey [1]) dayKey [1]).verifiable ∧
      (TransferRawEffectsSource01.volumeTail
        (installVolume (TransferCurrentVolumeSource01.withVolumeRead raw available entryKey)
          manager sct treeKey pendingKey payload) entryKey dayKey true child).cache.nonverifiable = child.cache.nonverifiable := by
  have frames := volume_payload_preserves_input_write_domains
    (TransferCurrentVolumeSource01.withVolumeRead raw available entryKey) manager sct treeKey pendingKey payload
    {child with cache := (TransferRawEffectsSource01.putV
      (TransferRawEffectsSource01.putV child.cache entryKey [1]) dayKey [1])} source
  simpa only [TransferRawEffectsSource01.volumeTail, installVolume,
    TransferNoteManagerSource01.installVolume, TransferCurrentVolumeSource01.withVolumeRead,
    ↓reduceIte, captured, TransferRawEffectsSource01.recordVolume, fresh, next,
    TransferRawEffectsSource01.liftCallback] using frames

theorem tail_preserves_nv_and_only_adds_volume_markers {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (treeKey pendingKey payload entryKey dayKey : Nat) (child : Delta O E) :
    (TransferRawEffectsSource01.volumeTail
      (installVolume (TransferCurrentVolumeSource01.withVolumeRead raw available entryKey)
        manager sct treeKey pendingKey payload) entryKey dayKey true child).cache.nonverifiable = child.cache.nonverifiable ∧
      ((TransferRawEffectsSource01.volumeTail
        (installVolume (TransferCurrentVolumeSource01.withVolumeRead raw available entryKey)
          manager sct treeKey pendingKey payload) entryKey dayKey true child).cache.verifiable = child.cache.verifiable ∨
       (TransferRawEffectsSource01.volumeTail
        (installVolume (TransferCurrentVolumeSource01.withVolumeRead raw available entryKey)
          manager sct treeKey pendingKey payload) entryKey dayKey true child).cache.verifiable =
          (TransferRawEffectsSource01.putV (TransferRawEffectsSource01.putV child.cache entryKey [1]) dayKey [1]).verifiable) := by
  cases captured : raw.currentSource child with
  | none =>
    simp [TransferRawEffectsSource01.volumeTail, installVolume, TransferNoteManagerSource01.installVolume,
      TransferCurrentVolumeSource01.withVolumeRead, captured]
  | some source =>
    cases read : TransferCurrentVolumeSource01.readVolume available entryKey child with
    | none =>
      simp [TransferRawEffectsSource01.volumeTail, installVolume, TransferNoteManagerSource01.installVolume,
        TransferCurrentVolumeSource01.withVolumeRead, captured, TransferRawEffectsSource01.recordVolume, read, next]
    | some spent =>
      cases spent with
      | true =>
        simp [TransferRawEffectsSource01.volumeTail, installVolume, TransferNoteManagerSource01.installVolume,
          TransferCurrentVolumeSource01.withVolumeRead, captured, TransferRawEffectsSource01.recordVolume, read, next]
      | false =>
        have frames := fresh_tail_retains_two_writes_on_any_return raw manager sct available
          treeKey pendingKey payload entryKey dayKey child source captured read
        exact ⟨frames.2, Or.inr frames.1⟩

theorem successful_read_derives_availability_and_absence {O E : Type}
    (available : Delta O E → Bool) (entryKey : Nat) (child : Delta O E)
    (fresh : TransferCurrentVolumeSource01.readVolume available entryKey child = some false) :
    available child = true ∧ (applyCache child.parent child.cache).verifiable entryKey = none := by
  cases readable : available child with
  | false => simp [TransferCurrentVolumeSource01.readVolume, readable] at fresh
  | true =>
    cases present : (applyCache child.parent child.cache).verifiable entryKey with
    | none => exact ⟨rfl, rfl⟩
    | some bytes => simp [TransferCurrentVolumeSource01.readVolume, readable, present] at fresh

theorem successful_tail_derives_actual_read_and_markers {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (treeKey pendingKey payload entryKey dayKey : Nat) (child : Delta O E)
    (success : (TransferRawEffectsSource01.volumeTail
      (installVolume (TransferCurrentVolumeSource01.withVolumeRead raw available entryKey)
        manager sct treeKey pendingKey payload) entryKey dayKey true child).result = .ok ()) :
    TransferCurrentVolumeSource01.readVolume available entryKey child = some false ∧
      (TransferRawEffectsSource01.volumeTail
        (installVolume (TransferCurrentVolumeSource01.withVolumeRead raw available entryKey)
          manager sct treeKey pendingKey payload) entryKey dayKey true child).cache.verifiable =
          (TransferRawEffectsSource01.putV (TransferRawEffectsSource01.putV child.cache entryKey [1]) dayKey [1]).verifiable := by
  cases captured : raw.currentSource child with
  | none =>
    simp [TransferRawEffectsSource01.volumeTail, installVolume, TransferNoteManagerSource01.installVolume,
      TransferCurrentVolumeSource01.withVolumeRead, captured] at success
  | some source =>
    cases read : TransferCurrentVolumeSource01.readVolume available entryKey child with
    | none =>
      simp [TransferRawEffectsSource01.volumeTail, installVolume, TransferNoteManagerSource01.installVolume,
        TransferCurrentVolumeSource01.withVolumeRead, captured, TransferRawEffectsSource01.recordVolume, read, next] at success
    | some spent =>
      cases spent with
      | true =>
        simp [TransferRawEffectsSource01.volumeTail, installVolume, TransferNoteManagerSource01.installVolume,
          TransferCurrentVolumeSource01.withVolumeRead, captured, TransferRawEffectsSource01.recordVolume, read, next] at success
      | false =>
        exact ⟨rfl, (fresh_tail_retains_two_writes_on_any_return raw manager sct available
          treeKey pendingKey payload entryKey dayKey child source captured read).1⟩

theorem execution_preserves_nv_and_only_adds_volume_markers {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (exactMatched : Bool) (child : Delta O E) (inputs outputs : List Nat) :
    (execute raw notes volume sct available wordMax capacity treeKey notesKey volumeKey payload nullifierKey
      entryKey dayKey exactMatched child inputs outputs).cache.nonverifiable = child.cache.nonverifiable ∧
      ((execute raw notes volume sct available wordMax capacity treeKey notesKey volumeKey payload nullifierKey
        entryKey dayKey exactMatched child inputs outputs).cache.verifiable = child.cache.verifiable ∨
       (execute raw notes volume sct available wordMax capacity treeKey notesKey volumeKey payload nullifierKey
        entryKey dayKey exactMatched child inputs outputs).cache.verifiable =
          (TransferRawEffectsSource01.putV (TransferRawEffectsSource01.putV child.cache entryKey [1]) dayKey [1]).verifiable) := by
  cases exactMatched with
  | false => exact ⟨rfl, Or.inl rfl⟩
  | true =>
    have frames :
        (TransferRawEffectsSource01.reshape
          (installBoth raw notes volume sct available treeKey notesKey volumeKey payload entryKey)
          wordMax capacity nullifierKey child inputs outputs).cache.verifiable = child.cache.verifiable ∧
        (TransferRawEffectsSource01.reshape
          (installBoth raw notes volume sct available treeKey notesKey volumeKey payload entryKey)
          wordMax capacity nullifierKey child inputs outputs).cache.nonverifiable = child.cache.nonverifiable :=
      TransferRawSourceFrames01.reshape_preserves_input_write_domains
        (installVolume (TransferCurrentVolumeSource01.withVolumeRead raw available entryKey)
          volume sct treeKey volumeKey payload) notes sct wordMax capacity treeKey notesKey nullifierKey child inputs outputs
    cases result : (TransferRawEffectsSource01.reshape
      (installBoth raw notes volume sct available treeKey notesKey volumeKey payload entryKey)
      wordMax capacity nullifierKey child inputs outputs).result with
    | error error =>
      simp only [execute, TransferRawEffectsSource01.executeTransfer, ↓reduceIte, result, next]
      exact ⟨frames.2, Or.inl frames.1⟩
    | ok returnedUnit =>
      cases returnedUnit
      have suffix := tail_preserves_nv_and_only_adds_volume_markers raw volume sct available treeKey volumeKey payload entryKey dayKey
        {child with cache := (TransferRawEffectsSource01.reshape
          (installBoth raw notes volume sct available treeKey notesKey volumeKey payload entryKey)
          wordMax capacity nullifierKey child inputs outputs).cache}
      simp only [execute, TransferRawEffectsSource01.executeTransfer, ↓reduceIte, result, next,
        tail_installBoth]
      refine ⟨suffix.1.trans frames.2, ?_⟩
      rcases suffix.2 with unchanged | marked
      · exact Or.inl (unchanged.trans frames.1)
      · apply Or.inr
        simpa only [TransferRawEffectsSource01.putV, frames.1] using marked

theorem execution_success_derives_fresh_input_and_two_writes {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (available : Delta O E → Bool)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (exactMatched : Bool) (child : Delta O E) (inputs outputs : List Nat)
    (success : (execute raw notes volume sct available wordMax capacity treeKey notesKey volumeKey payload nullifierKey
      entryKey dayKey exactMatched child inputs outputs).result = .ok ()) :
    exactMatched = true ∧ (applyCache child.parent child.cache).verifiable entryKey = none ∧
      (execute raw notes volume sct available wordMax capacity treeKey notesKey volumeKey payload nullifierKey
        entryKey dayKey exactMatched child inputs outputs).cache.verifiable =
          (TransferRawEffectsSource01.putV (TransferRawEffectsSource01.putV child.cache entryKey [1]) dayKey [1]).verifiable ∧
      (execute raw notes volume sct available wordMax capacity treeKey notesKey volumeKey payload nullifierKey
        entryKey dayKey exactMatched child inputs outputs).cache.nonverifiable = child.cache.nonverifiable := by
  cases exactMatched with
  | false => simp [execute, TransferRawEffectsSource01.executeTransfer] at success
  | true =>
    have frames :
        (TransferRawEffectsSource01.reshape
          (installBoth raw notes volume sct available treeKey notesKey volumeKey payload entryKey)
          wordMax capacity nullifierKey child inputs outputs).cache.verifiable = child.cache.verifiable ∧
        (TransferRawEffectsSource01.reshape
          (installBoth raw notes volume sct available treeKey notesKey volumeKey payload entryKey)
          wordMax capacity nullifierKey child inputs outputs).cache.nonverifiable = child.cache.nonverifiable :=
      TransferRawSourceFrames01.reshape_preserves_input_write_domains
        (installVolume (TransferCurrentVolumeSource01.withVolumeRead raw available entryKey)
          volume sct treeKey volumeKey payload) notes sct wordMax capacity treeKey notesKey nullifierKey child inputs outputs
    cases result : (TransferRawEffectsSource01.reshape
      (installBoth raw notes volume sct available treeKey notesKey volumeKey payload entryKey)
      wordMax capacity nullifierKey child inputs outputs).result with
    | error error => simp only [execute, TransferRawEffectsSource01.executeTransfer, ↓reduceIte, result, next] at success; contradiction
    | ok returnedUnit =>
      cases returnedUnit
      simp only [execute, TransferRawEffectsSource01.executeTransfer, ↓reduceIte, result, next,
        tail_installBoth] at success ⊢
      have tail := successful_tail_derives_actual_read_and_markers raw volume sct available treeKey volumeKey payload entryKey dayKey
        {child with cache := (TransferRawEffectsSource01.reshape
          (installBoth raw notes volume sct available treeKey notesKey volumeKey payload entryKey)
          wordMax capacity nullifierKey child inputs outputs).cache} success
      have fresh := successful_read_derives_availability_and_absence available entryKey _ tail.1
      have suffix := tail_preserves_nv_and_only_adds_volume_markers raw volume sct available treeKey volumeKey payload entryKey dayKey
        {child with cache := (TransferRawEffectsSource01.reshape
          (installBoth raw notes volume sct available treeKey notesKey volumeKey payload entryKey)
          wordMax capacity nullifierKey child inputs outputs).cache}
      refine ⟨True.intro, ?_, ?_, suffix.1.trans frames.2⟩
      · simpa only [applyCache, frames.1] using fresh.2
      · simpa only [TransferRawEffectsSource01.putV, frames.1] using tail.2

set_option pp.all true in
#check @installVolume
#print axioms installVolume
set_option pp.all true in
#check @installBoth
#print axioms installBoth
set_option pp.all true in
#check @execute
#print axioms execute
set_option pp.all true in
#check @volume_payload_preserves_input_write_domains
#print axioms volume_payload_preserves_input_write_domains
set_option pp.all true in
#check @tail_ignores_note_callback
#print axioms tail_ignores_note_callback
set_option pp.all true in
#check @tail_installBoth
#print axioms tail_installBoth
set_option pp.all true in
#check @fresh_tail_retains_two_writes_on_any_return
#print axioms fresh_tail_retains_two_writes_on_any_return
set_option pp.all true in
#check @tail_preserves_nv_and_only_adds_volume_markers
#print axioms tail_preserves_nv_and_only_adds_volume_markers
set_option pp.all true in
#check @successful_read_derives_availability_and_absence
#print axioms successful_read_derives_availability_and_absence
set_option pp.all true in
#check @successful_tail_derives_actual_read_and_markers
#print axioms successful_tail_derives_actual_read_and_markers
set_option pp.all true in
#check @execution_preserves_nv_and_only_adds_volume_markers
#print axioms execution_preserves_nv_and_only_adds_volume_markers
set_option pp.all true in
#check @execution_success_derives_fresh_input_and_two_writes
#print axioms execution_success_derives_fresh_input_and_two_writes

end ShielddSecurity.TransferOrdinaryStorageSource01
