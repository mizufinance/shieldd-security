import ShielddSecurity.TransferSctInsertionSource01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferRawSourceFrames01

open TransferStateDelta TransferRawStateProgram01

/-! Derive storage-domain frames from source primitives, including returned
errors. This scope uses the successfully loaded immutable SCT branch and
explicit pending-object updates; getter panic, Rust Clone/COW, actual key/value
codecs and tree/reader semantics remain inherited interfaces. It is a raw
action cache result, not block-finalization or durable-store framing. -/

def installNotes {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (treeKey pendingKey : Nat) :
    TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X) :=
  TransferNoteManagerSource01.installNotes raw
    (TransferSctInsertionSource01.installSct manager sct treeKey) pendingKey

theorem sct_insertion_preserves_input_write_domains {O E X Tree : Type}
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (treeKey : Nat)
    (child : Delta O E) (tree : Tree) (commitment : Nat) (source : Bool) :
    (TransferSctInsertionSource01.insertLoaded sct treeKey child tree commitment source).cache.verifiable = child.cache.verifiable ∧
      (TransferSctInsertionSource01.insertLoaded sct treeKey child tree commitment source).cache.nonverifiable = child.cache.nonverifiable := by
  cases capacity : TransferSctInsertionSource01.checkCapacity (X := X) (sct.position tree) with
  | error error => simp only [TransferSctInsertionSource01.insertLoaded, capacity]
  | ok returnedUnit =>
    cases returnedUnit
    cases inserted : sct.localInsert tree commitment with
    | error error => simp only [TransferSctInsertionSource01.insertLoaded, capacity, inserted]
    | ok pair =>
      rcases pair with ⟨updatedTree, position⟩
      simp only [TransferSctInsertionSource01.insertLoaded, capacity, inserted,
        TransferRawEffectsSource01.emit, putObject]

theorem manager_preserves_input_write_domains {O E X Tree : Type}
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (treeKey pendingKey : Nat)
    (child : Delta O E) (payload : Nat) (source : Bool) :
    (TransferNoteManagerSource01.insertPayload
      (TransferSctInsertionSource01.installSct manager sct treeKey) pendingKey child payload source).cache.verifiable = child.cache.verifiable ∧
      (TransferNoteManagerSource01.insertPayload
        (TransferSctInsertionSource01.installSct manager sct treeKey) pendingKey child payload source).cache.nonverifiable = child.cache.nonverifiable := by
  have frames := sct_insertion_preserves_input_write_domains sct treeKey child (sct.loaded child) payload source
  cases result : (TransferSctInsertionSource01.insertLoaded sct treeKey child (sct.loaded child) payload source).result with
  | error error =>
      simpa only [TransferNoteManagerSource01.insertPayload, TransferSctInsertionSource01.installSct, result] using frames
  | ok position =>
      simpa only [TransferNoteManagerSource01.insertPayload, TransferSctInsertionSource01.installSct, result, putObject] using frames

theorem all_note_outputs_preserve_input_write_domains {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (treeKey pendingKey : Nat)
    (source : Bool) (child : Delta O E) (outputs : List Nat) :
    (TransferRawEffectsSource01.notes (installNotes raw manager sct treeKey pendingKey) source child outputs).cache.verifiable = child.cache.verifiable ∧
      (TransferRawEffectsSource01.notes (installNotes raw manager sct treeKey pendingKey) source child outputs).cache.nonverifiable = child.cache.nonverifiable := by
  induction outputs generalizing child with
  | nil => exact ⟨rfl, rfl⟩
  | cons output rest ih =>
    have frames := manager_preserves_input_write_domains manager sct treeKey pendingKey child output source
    cases result : (TransferNoteManagerSource01.insertPayload
      (TransferSctInsertionSource01.installSct manager sct treeKey) pendingKey child output source).result with
    | error error =>
      simpa only [TransferRawEffectsSource01.notes, installNotes, TransferNoteManagerSource01.installNotes,
        TransferRawEffectsSource01.liftCallback, result, next] using frames
    | ok returnedUnit =>
      cases returnedUnit
      have suffix := ih {child with cache := TransferRawEffectsSource01.emit
        (TransferNoteManagerSource01.insertPayload (TransferSctInsertionSource01.installSct manager sct treeKey)
          pendingKey child output source).cache (raw.noteEvent output)}
      refine ⟨?_, ?_⟩
      · simpa only [TransferRawEffectsSource01.notes, installNotes, TransferNoteManagerSource01.installNotes,
          TransferRawEffectsSource01.liftCallback, result, next] using suffix.1.trans frames.1
      · simpa only [TransferRawEffectsSource01.notes, installNotes, TransferNoteManagerSource01.installNotes,
          TransferRawEffectsSource01.liftCallback, result, next] using suffix.2.trans frames.2

theorem nullifier_batch_preserves_input_write_domains {O E : Type}
    (backend : TransferNullifierBatchSource01.Backend O E) (wordMax capacity pendingKey : Nat)
    (source : Bool) (child : Delta O E) (inputs : List Nat) :
    (TransferNullifierBatchSource01.executeNullify backend wordMax capacity pendingKey source child inputs).cache.verifiable = child.cache.verifiable ∧
      (TransferNullifierBatchSource01.executeNullify backend wordMax capacity pendingKey source child inputs).cache.nonverifiable = child.cache.nonverifiable := by
  cases empty : inputs.isEmpty with
  | true => simp only [TransferNullifierBatchSource01.executeNullify, empty, ↓reduceIte]
  | false =>
    cases source with
    | false => simp only [TransferNullifierBatchSource01.executeNullify, empty, ↓reduceIte]
    | true =>
      cases checked : TransferNullifierBatchSource01.inspect backend wordMax capacity child inputs with
      | error error => simp only [TransferNullifierBatchSource01.executeNullify, empty, ↓reduceIte, checked]
      | ok pending => simp only [TransferNullifierBatchSource01.executeNullify, empty, ↓reduceIte, checked, putObject]

theorem reshape_preserves_input_write_domains {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree)
    (wordMax capacity treeKey pendingKey nullifierKey : Nat) (child : Delta O E) (inputs outputs : List Nat) :
    (TransferRawEffectsSource01.reshape (installNotes raw manager sct treeKey pendingKey)
      wordMax capacity nullifierKey child inputs outputs).cache.verifiable = child.cache.verifiable ∧
      (TransferRawEffectsSource01.reshape (installNotes raw manager sct treeKey pendingKey)
        wordMax capacity nullifierKey child inputs outputs).cache.nonverifiable = child.cache.nonverifiable := by
  cases source : raw.currentSource child with
  | none => simp only [TransferRawEffectsSource01.reshape, installNotes, TransferNoteManagerSource01.installNotes, source]
  | some sourceHasId =>
    have frames := nullifier_batch_preserves_input_write_domains raw.nullifiers wordMax capacity nullifierKey sourceHasId child inputs
    cases result : (TransferNullifierBatchSource01.executeNullify raw.nullifiers wordMax capacity nullifierKey sourceHasId child inputs).result with
    | error error =>
      simpa only [TransferRawEffectsSource01.reshape, installNotes, TransferNoteManagerSource01.installNotes, source, result] using frames
    | ok returnedUnit =>
      cases returnedUnit
      have emitted := TransferRawEffectsSource01.emitSpends_exact raw.spentEvent
        (TransferNullifierBatchSource01.executeNullify raw.nullifiers wordMax capacity nullifierKey sourceHasId child inputs).cache inputs
      have notesFrame := all_note_outputs_preserve_input_write_domains raw manager sct treeKey pendingKey sourceHasId
        {child with cache := TransferRawEffectsSource01.emitSpends raw.spentEvent
          (TransferNullifierBatchSource01.executeNullify raw.nullifiers wordMax capacity nullifierKey sourceHasId child inputs).cache inputs} outputs
      rw [emitted] at notesFrame
      refine ⟨?_, ?_⟩
      · simpa only [TransferRawEffectsSource01.reshape, installNotes, TransferNoteManagerSource01.installNotes, source, result, emitted] using notesFrame.1.trans frames.1
      · simpa only [TransferRawEffectsSource01.reshape, installNotes, TransferNoteManagerSource01.installNotes, source, result, emitted] using notesFrame.2.trans frames.2

theorem fee_funding_preserves_input_write_domains_on_any_return {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree)
    (wordMax capacity treeKey pendingKey nullifierKey entryKey dayKey : Nat)
    (exactMatched : Bool) (child : Delta O E) (inputs outputs : List Nat) :
    (TransferRawEffectsSource01.executeTransfer (installNotes raw manager sct treeKey pendingKey)
      wordMax capacity nullifierKey entryKey dayKey exactMatched false child inputs outputs).cache.verifiable = child.cache.verifiable ∧
      (TransferRawEffectsSource01.executeTransfer (installNotes raw manager sct treeKey pendingKey)
        wordMax capacity nullifierKey entryKey dayKey exactMatched false child inputs outputs).cache.nonverifiable = child.cache.nonverifiable := by
  cases exactMatched with
  | false => exact ⟨rfl, rfl⟩
  | true =>
    have frames := reshape_preserves_input_write_domains raw manager sct wordMax capacity treeKey pendingKey nullifierKey child inputs outputs
    cases result : (TransferRawEffectsSource01.reshape (installNotes raw manager sct treeKey pendingKey)
      wordMax capacity nullifierKey child inputs outputs).result with
    | error error => simpa only [TransferRawEffectsSource01.executeTransfer, ↓reduceIte, result, next] using frames
    | ok returnedUnit =>
      cases returnedUnit
      simpa only [TransferRawEffectsSource01.executeTransfer, ↓reduceIte, result, next,
        TransferRawEffectsSource01.fee_funding_skips_volume_tail] using frames

set_option pp.all true in
#check @installNotes
#print axioms installNotes
set_option pp.all true in
#check @sct_insertion_preserves_input_write_domains
#print axioms sct_insertion_preserves_input_write_domains
set_option pp.all true in
#check @manager_preserves_input_write_domains
#print axioms manager_preserves_input_write_domains
set_option pp.all true in
#check @all_note_outputs_preserve_input_write_domains
#print axioms all_note_outputs_preserve_input_write_domains
set_option pp.all true in
#check @nullifier_batch_preserves_input_write_domains
#print axioms nullifier_batch_preserves_input_write_domains
set_option pp.all true in
#check @reshape_preserves_input_write_domains
#print axioms reshape_preserves_input_write_domains
set_option pp.all true in
#check @fee_funding_preserves_input_write_domains_on_any_return
#print axioms fee_funding_preserves_input_write_domains_on_any_return

end ShielddSecurity.TransferRawSourceFrames01
