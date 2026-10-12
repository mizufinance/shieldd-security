import ShielddSecurity.TransferDeferredBodyFailure01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferWholeNullifierAdmission01
open TransferStateDelta TransferRawStateProgram01 TransferIndexWriterModel01
open TransferVerificationEqualitySource01 (Item)

/-! Whole successful delivery, in either proof context and any index mode,
derives successful source-order nullifier admission for every action input.
No successful primitive callback, fresh-input predicate, inspected pending
value or desired capacity result is supplied. Actual authenticated reader,
source/token/extractor/keys/bytes/ownership/tree/native/durability semantics
remain interfaces; batch admission is not final durable nullifier publication. -/

def installedBackend {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (treeKey notesKey volumeKey payload entryKey : Nat) (context : TransferCapabilitySource01.ProofContext) :
    TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X) :=
  match context with
  | .ordinary => TransferOrdinaryStorageSource01.installBoth raw notes volume sct volumeAvailable treeKey notesKey volumeKey payload entryKey
  | .feeFunding => TransferRawSourceFrames01.installNotes raw notes sct treeKey notesKey

theorem installed_backend_retains_original_source_and_nullifiers {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (treeKey notesKey volumeKey payload entryKey : Nat) (context : TransferCapabilitySource01.ProofContext) :
    (installedBackend raw notes volume sct volumeAvailable treeKey notesKey volumeKey payload entryKey context).currentSource = raw.currentSource ∧
    (installedBackend raw notes volume sct volumeAvailable treeKey notesKey volumeKey payload entryKey context).nullifiers = raw.nullifiers := by
  cases context <;> exact ⟨rfl, rfl⟩

theorem branch_is_exact_complete_item_capability_program {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item) (child : Delta O E) :
    TransferDeferredBodyFailure01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity
      treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item child =
    TransferCapabilitySource01.execute (installedBackend raw notes volume sct volumeAvailable treeKey notesKey volumeKey payload entryKey context)
      extract inputs outputs wordMax capacity nullifierKey entryKey dayKey action ⟨item, context⟩ child := by
  cases context <;> rfl

theorem successful_transfer_derives_reshape_success {O E X : Type}
    (backend : TransferRawEffectsSource01.Backend O E X)
    (wordMax capacity nullifierKey entryKey dayKey : Nat) (ordinary : Bool)
    (child : Delta O E) (inputs outputs : List Nat)
    (success : (TransferRawEffectsSource01.executeTransfer backend wordMax capacity nullifierKey entryKey dayKey
      true ordinary child inputs outputs).result = .ok ()) :
    (TransferRawEffectsSource01.reshape backend wordMax capacity nullifierKey child inputs outputs).result = .ok () := by
  change (next (TransferRawEffectsSource01.reshape backend wordMax capacity nullifierKey child inputs outputs)
    (fun updated => TransferRawEffectsSource01.volumeTail backend entryKey dayKey ordinary {child with cache := updated})).result = .ok () at success
  cases result : (TransferRawEffectsSource01.reshape backend wordMax capacity nullifierKey child inputs outputs).result with
  | error error => simp only [next, result] at success; contradiction
  | ok returnedUnit => cases returnedUnit; rfl

theorem successful_bound_body_derives_reextraction_and_reshape {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item) (child : Delta O E)
    (success : (TransferDeferredBodyFailure01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity
      treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item child).result = .ok ()) :
    extract action context = .ok item ∧
      (TransferRawEffectsSource01.reshape (installedBackend raw notes volume sct volumeAvailable treeKey notesKey volumeKey payload entryKey context)
        wordMax capacity nullifierKey child (inputs action) (outputs action)).result = .ok () := by
  rw [branch_is_exact_complete_item_capability_program] at success
  have extracted := TransferCapabilitySource01.successful_execution_derives_exact_reextraction _ extract inputs outputs
    wordMax capacity nullifierKey entryKey dayKey action ⟨item, context⟩ child success
  rw [TransferCapabilitySource01.exact_rebinding_dispatches_projected_action _ extract inputs outputs
    wordMax capacity nullifierKey entryKey dayKey action ⟨item, context⟩ child extracted] at success
  cases result : (TransferRawEffectsSource01.executeTransfer
      (installedBackend raw notes volume sct volumeAvailable treeKey notesKey volumeKey payload entryKey context)
      wordMax capacity nullifierKey entryKey dayKey true (TransferCapabilitySource01.isOrdinary context)
      child (inputs action) (outputs action)).result with
  | error error => simp only [TransferCapabilitySource01.liftRaw, result] at success; contradiction
  | ok returnedUnit =>
    cases returnedUnit
    exact ⟨extracted, successful_transfer_derives_reshape_success _ wordMax capacity nullifierKey entryKey dayKey
      (TransferCapabilitySource01.isOrdinary context) child (inputs action) (outputs action) result⟩

theorem whole_delivery_success_derives_every_input_fresh_and_bounded {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (convert : A → Option Encoded) (indexAvailable : Delta O E → Nat → Bool)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (mode : IndexMode) (parent : State O) (queued : List A) (committed : Commit O E A)
    (nonempty : (inputs action).isEmpty = false) (belowWord : capacity < wordMax)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (TransferDeferredBodyFailure01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey
        volumeKey payload nullifierKey entryKey dayKey context action item)) registryMatches exclusive mode action parent queued = some committed) :
    registryMatches = true ∧ exclusive = true ∧ extract action context = .ok item ∧
      ∃ pending : TransferNullifierBatchSource01.Pending,
        raw.currentSource ⟨parent, empty⟩ = some true ∧
        TransferNullifierBatchSource01.inspect raw.nullifiers wordMax capacity ⟨parent, empty⟩ (inputs action) = .ok pending ∧
        TransferNullifierBatchSource01.uniqueLoop [] (inputs action) = true ∧
        pending.ordered = (raw.nullifiers.pending ⟨parent, empty⟩).ordered ++ inputs action ∧
        pending.ordered.length ≤ capacity ∧ pending.sealed = false ∧
        ∀ key ∈ inputs action, raw.nullifiers.lookup ⟨parent, empty⟩ key = some false ∧
          (raw.nullifiers.pending ⟨parent, empty⟩).membership key = false ∧ pending.membership key = true := by
  obtain ⟨registry, unique, executed, _, performed, _, _, _, _⟩ :=
    successful_delivery_order _ registryMatches exclusive mode action parent queued committed success
  change asCache (TransferDeferredBodyFailure01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey
    volumeKey payload nullifierKey entryKey dayKey context action item ⟨parent, empty⟩) = some executed at performed
  have bodySuccess := (TransferOrdinaryIndexDelivery01.selected_cache_derives_success _ executed performed).1
  obtain ⟨extracted, reshaped⟩ := successful_bound_body_derives_reextraction_and_reshape raw notes volume sct volumeAvailable extract inputs outputs
    wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item ⟨parent, empty⟩ bodySuccess
  have projections := installed_backend_retains_original_source_and_nullifiers raw notes volume sct volumeAvailable
    treeKey notesKey volumeKey payload entryKey context
  cases source : raw.currentSource ⟨parent, (empty : Cache O E)⟩ with
  | none => simp only [TransferRawEffectsSource01.reshape, projections.1, source] at reshaped; contradiction
  | some sourceHasId =>
    cases batch : TransferNullifierBatchSource01.executeNullify raw.nullifiers wordMax capacity nullifierKey sourceHasId
        ⟨parent, (empty : Cache O E)⟩ (inputs action) with
    | mk cache result =>
      cases result with
      | error error =>
        simp only [TransferRawEffectsSource01.reshape, projections.1, projections.2, source, batch] at reshaped
        contradiction
      | ok returnedUnit =>
        cases returnedUnit
        obtain ⟨transactional, pending, inspected, _⟩ := TransferNullifierBatchSource01.successful_nonempty_batch_single_object_write
          raw.nullifiers wordMax capacity nullifierKey sourceHasId ⟨parent, empty⟩ (inputs action) cache nonempty batch
        have admission := TransferNullifierBatchSource01.inspection_success_capacity_and_all_inputs raw.nullifiers wordMax capacity
          ⟨parent, empty⟩ (inputs action) pending belowWord inspected
        obtain ⟨_, _, _, distinct, _, _, _, _, _, _⟩ := TransferNullifierBatchSource01.inspection_success_order
          raw.nullifiers wordMax capacity ⟨parent, empty⟩ (inputs action) pending inspected
        exact ⟨registry, unique, extracted, pending, by rw [transactional],
          inspected, distinct, admission⟩

set_option pp.all true in
#check @installedBackend
#print axioms installedBackend
set_option pp.all true in
#check @installed_backend_retains_original_source_and_nullifiers
#print axioms installed_backend_retains_original_source_and_nullifiers
set_option pp.all true in
#check @branch_is_exact_complete_item_capability_program
#print axioms branch_is_exact_complete_item_capability_program
set_option pp.all true in
#check @successful_transfer_derives_reshape_success
#print axioms successful_transfer_derives_reshape_success
set_option pp.all true in
#check @successful_bound_body_derives_reextraction_and_reshape
#print axioms successful_bound_body_derives_reextraction_and_reshape
set_option pp.all true in
#check @whole_delivery_success_derives_every_input_fresh_and_bounded
#print axioms whole_delivery_success_derives_every_input_fresh_and_bounded
end ShielddSecurity.TransferWholeNullifierAdmission01
