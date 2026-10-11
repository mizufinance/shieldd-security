import ShielddSecurity.TransferWholeNullifierAdmission01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferPendingNullifierRetention01
open TransferStateDelta TransferRawStateProgram01 TransferIndexWriterModel01
open TransferVerificationEqualitySource01 (Item)

/-! Later SCT/note/volume operations frame a distinct pending-nullifier object
for every returned outcome. Whole successful action delivery then retains the
actual admitted pending encoding through every index mode. Key separation,
immutable object/codec/reader/token/crypto/Rust ownership/Host/native/durable
store correspondence remain interfaces. This is visible staged state, not
durable publication. All recurrences are symbolic and heartbeat bounded. -/

theorem sct_any_return_frames_other_object {O E X Tree : Type}
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (treeKey other : Nat)
    (child : Delta O E) (tree : Tree) (payload : Nat) (source : Bool) (different : other ≠ treeKey) :
    (TransferSctInsertionSource01.insertLoaded sct treeKey child tree payload source).cache.objects other = child.cache.objects other := by
  cases capacity : TransferSctInsertionSource01.checkCapacity (X := X) (sct.position tree) with
  | error error => simp [TransferSctInsertionSource01.insertLoaded, capacity]
  | ok returnedUnit =>
    cases returnedUnit
    cases inserted : sct.localInsert tree payload with
    | error error => simp [TransferSctInsertionSource01.insertLoaded, capacity, inserted]
    | ok pair =>
      rcases pair with ⟨updatedTree, position⟩
      simp [TransferSctInsertionSource01.insertLoaded, capacity, inserted, TransferRawEffectsSource01.emit, putObject, different]

theorem manager_any_return_frames_other_object {O E X Tree : Type}
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (treeKey pendingKey other : Nat)
    (child : Delta O E) (payload : Nat) (source : Bool) (notTree : other ≠ treeKey) (notPending : other ≠ pendingKey) :
    (TransferNoteManagerSource01.insertPayload (TransferSctInsertionSource01.installSct manager sct treeKey)
      pendingKey child payload source).cache.objects other = child.cache.objects other := by
  have frame := sct_any_return_frames_other_object sct treeKey other child (sct.loaded child) payload source notTree
  cases result : (TransferSctInsertionSource01.insertLoaded sct treeKey child (sct.loaded child) payload source).result with
  | error error =>
    simpa only [TransferNoteManagerSource01.insertPayload, TransferSctInsertionSource01.installSct, result] using frame
  | ok position =>
    simpa only [TransferNoteManagerSource01.insertPayload, TransferSctInsertionSource01.installSct, result, putObject, if_neg notPending] using frame

theorem all_notes_any_return_frames_other_object {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (treeKey pendingKey other : Nat)
    (source : Bool) (child : Delta O E) (outputs : List Nat) (notTree : other ≠ treeKey) (notPending : other ≠ pendingKey) :
    (TransferRawEffectsSource01.notes (TransferRawSourceFrames01.installNotes raw manager sct treeKey pendingKey)
      source child outputs).cache.objects other = child.cache.objects other := by
  induction outputs generalizing child with
  | nil => rfl
  | cons output rest ih =>
    have first := manager_any_return_frames_other_object manager sct treeKey pendingKey other child output source notTree notPending
    cases result : (TransferNoteManagerSource01.insertPayload (TransferSctInsertionSource01.installSct manager sct treeKey)
        pendingKey child output source).result with
    | error error =>
      simpa only [TransferRawEffectsSource01.notes, TransferRawSourceFrames01.installNotes, TransferNoteManagerSource01.installNotes,
        TransferRawEffectsSource01.liftCallback, result, next] using first
    | ok returnedUnit =>
      cases returnedUnit
      have later := ih {child with cache := TransferRawEffectsSource01.emit
        (TransferNoteManagerSource01.insertPayload (TransferSctInsertionSource01.installSct manager sct treeKey)
          pendingKey child output source).cache (raw.noteEvent output)}
      simpa only [TransferRawEffectsSource01.notes, TransferRawSourceFrames01.installNotes, TransferNoteManagerSource01.installNotes,
        TransferRawEffectsSource01.liftCallback, result, next] using later.trans first

theorem record_volume_any_return_preserves_objects {O E X : Type}
    (raw : TransferRawEffectsSource01.Backend O E X) (entryKey dayKey : Nat) (child : Delta O E) :
    (TransferRawEffectsSource01.recordVolume raw entryKey dayKey child).cache.objects = child.cache.objects := by
  cases read : raw.volumePresent child with
  | none => simp [TransferRawEffectsSource01.recordVolume, read]
  | some spent => cases spent <;> simp [TransferRawEffectsSource01.recordVolume, read, TransferRawEffectsSource01.putV]

theorem ordinary_volume_tail_any_return_frames_other_object {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (manager : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree)
    (treeKey pendingKey payload entryKey dayKey other : Nat) (child : Delta O E)
    (notTree : other ≠ treeKey) (notPending : other ≠ pendingKey) :
    (TransferRawEffectsSource01.volumeTail (TransferOrdinaryStorageSource01.installVolume raw manager sct treeKey pendingKey payload)
      entryKey dayKey true child).cache.objects other = child.cache.objects other := by
  cases source : raw.currentSource child with
  | none => simp [TransferRawEffectsSource01.volumeTail, TransferOrdinaryStorageSource01.installVolume,
      TransferNoteManagerSource01.installVolume, source]
  | some sourceHasId =>
    have earlier := record_volume_any_return_preserves_objects raw entryKey dayKey child
    cases recorded : (TransferRawEffectsSource01.recordVolume raw entryKey dayKey child).result with
    | error error =>
      simpa only [TransferRawEffectsSource01.volumeTail, TransferOrdinaryStorageSource01.installVolume,
        TransferNoteManagerSource01.installVolume, source, ↓reduceIte, next, recorded] using congrFun earlier other
    | ok returnedUnit =>
      cases returnedUnit
      have later := manager_any_return_frames_other_object manager sct treeKey pendingKey other
        {child with cache := (TransferRawEffectsSource01.recordVolume raw entryKey dayKey child).cache}
        payload sourceHasId notTree notPending
      simpa only [TransferRawEffectsSource01.volumeTail, TransferOrdinaryStorageSource01.installVolume,
        TransferNoteManagerSource01.installVolume, source, ↓reduceIte, next, recorded,
        TransferRawEffectsSource01.liftCallback] using later.trans (congrFun earlier other)

theorem context_tail_any_return_frames_other_object {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (treeKey notesKey volumeKey payload entryKey dayKey other : Nat) (context : TransferCapabilitySource01.ProofContext)
    (child : Delta O E) (notTree : other ≠ treeKey) (notVolume : other ≠ volumeKey) :
    (TransferRawEffectsSource01.volumeTail (TransferWholeNullifierAdmission01.installedBackend raw notes volume sct volumeAvailable
      treeKey notesKey volumeKey payload entryKey context) entryKey dayKey (TransferCapabilitySource01.isOrdinary context) child).cache.objects other =
      child.cache.objects other := by
  cases context with
  | ordinary =>
    change (TransferRawEffectsSource01.volumeTail (TransferOrdinaryStorageSource01.installBoth raw notes volume sct volumeAvailable
      treeKey notesKey volumeKey payload entryKey) entryKey dayKey true child).cache.objects other = child.cache.objects other
    rw [TransferOrdinaryStorageSource01.tail_installBoth]
    exact ordinary_volume_tail_any_return_frames_other_object (TransferCurrentVolumeSource01.withVolumeRead raw volumeAvailable entryKey)
      volume sct treeKey volumeKey payload entryKey dayKey other child notTree notVolume
  | feeFunding => rfl

theorem successful_reshape_retains_admitted_pending_object {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (wordMax capacity treeKey notesKey nullifierKey : Nat)
    (child : Delta O E) (inputs outputs : List Nat) (nonempty : inputs.isEmpty = false)
    (notTree : nullifierKey ≠ treeKey) (notNotes : nullifierKey ≠ notesKey)
    (success : (TransferRawEffectsSource01.reshape (TransferRawSourceFrames01.installNotes raw notes sct treeKey notesKey)
      wordMax capacity nullifierKey child inputs outputs).result = .ok ()) :
    ∃ pending : TransferNullifierBatchSource01.Pending,
      TransferNullifierBatchSource01.inspect raw.nullifiers wordMax capacity child inputs = .ok pending ∧
      (TransferRawEffectsSource01.reshape (TransferRawSourceFrames01.installNotes raw notes sct treeKey notesKey)
        wordMax capacity nullifierKey child inputs outputs).cache.objects nullifierKey = some (some (raw.nullifiers.encode pending)) := by
  cases source : raw.currentSource child with
  | none => simp only [TransferRawEffectsSource01.reshape, TransferRawSourceFrames01.installNotes, TransferNoteManagerSource01.installNotes, source] at success; contradiction
  | some sourceHasId =>
    cases batch : TransferNullifierBatchSource01.executeNullify raw.nullifiers wordMax capacity nullifierKey sourceHasId child inputs with
    | mk cache result =>
      cases result with
      | error error =>
        simp only [TransferRawEffectsSource01.reshape, TransferRawSourceFrames01.installNotes, TransferNoteManagerSource01.installNotes, source, batch] at success
        contradiction
      | ok returnedUnit =>
        cases returnedUnit
        obtain ⟨_, pending, inspected, written⟩ := TransferNullifierBatchSource01.successful_nonempty_batch_single_object_write
          raw.nullifiers wordMax capacity nullifierKey sourceHasId child inputs cache nonempty batch
        have framed := all_notes_any_return_frames_other_object raw notes sct treeKey notesKey nullifierKey sourceHasId
          {child with cache := TransferRawEffectsSource01.emitSpends raw.spentEvent cache inputs} outputs notTree notNotes
        have staged : (TransferRawEffectsSource01.emitSpends raw.spentEvent cache inputs).objects nullifierKey =
            some (some (raw.nullifiers.encode pending)) := by
          rw [TransferRawEffectsSource01.emitSpends_exact, written]
          simp only [putObject, ite_true]
        refine ⟨pending, inspected, ?_⟩
        simpa only [TransferRawEffectsSource01.reshape, TransferRawSourceFrames01.installNotes, TransferNoteManagerSource01.installNotes,
          source, batch] using framed.trans staged

theorem successful_context_reshape_retains_admitted_pending_object {O E X Tree : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (child : Delta O E) (inputs outputs : List Nat)
    (nonempty : inputs.isEmpty = false) (notTree : nullifierKey ≠ treeKey) (notNotes : nullifierKey ≠ notesKey)
    (success : (TransferRawEffectsSource01.reshape (TransferWholeNullifierAdmission01.installedBackend raw notes volume sct volumeAvailable
      treeKey notesKey volumeKey payload entryKey context) wordMax capacity nullifierKey child inputs outputs).result = .ok ()) :
    ∃ pending : TransferNullifierBatchSource01.Pending,
      TransferNullifierBatchSource01.inspect raw.nullifiers wordMax capacity child inputs = .ok pending ∧
      (TransferRawEffectsSource01.reshape (TransferWholeNullifierAdmission01.installedBackend raw notes volume sct volumeAvailable
        treeKey notesKey volumeKey payload entryKey context) wordMax capacity nullifierKey child inputs outputs).cache.objects nullifierKey =
          some (some (raw.nullifiers.encode pending)) := by
  cases context with
  | ordinary =>
    exact successful_reshape_retains_admitted_pending_object
      (TransferOrdinaryStorageSource01.installVolume (TransferCurrentVolumeSource01.withVolumeRead raw volumeAvailable entryKey)
        volume sct treeKey volumeKey payload) notes sct wordMax capacity treeKey notesKey nullifierKey child inputs outputs nonempty notTree notNotes success
  | feeFunding =>
    exact successful_reshape_retains_admitted_pending_object raw notes sct wordMax capacity treeKey notesKey nullifierKey child inputs outputs
      nonempty notTree notNotes success

theorem successful_bound_body_retains_admitted_pending_object {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item) (child : Delta O E)
    (nonempty : (inputs action).isEmpty = false) (notTree : nullifierKey ≠ treeKey)
    (notNotes : nullifierKey ≠ notesKey) (notVolume : nullifierKey ≠ volumeKey)
    (success : (TransferDeferredBodyFailure01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey
      volumeKey payload nullifierKey entryKey dayKey context action item child).result = .ok ()) :
    ∃ pending : TransferNullifierBatchSource01.Pending,
      TransferNullifierBatchSource01.inspect raw.nullifiers wordMax capacity child (inputs action) = .ok pending ∧
      (TransferDeferredBodyFailure01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey
        volumeKey payload nullifierKey entryKey dayKey context action item child).cache.objects nullifierKey = some (some (raw.nullifiers.encode pending)) := by
  obtain ⟨extracted, reshaped⟩ := TransferWholeNullifierAdmission01.successful_bound_body_derives_reextraction_and_reshape raw notes volume sct volumeAvailable
    extract inputs outputs wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item child success
  obtain ⟨pending, inspected, retained⟩ := successful_context_reshape_retains_admitted_pending_object raw notes volume sct volumeAvailable wordMax capacity
    treeKey notesKey volumeKey payload nullifierKey entryKey context child (inputs action) (outputs action) nonempty notTree notNotes reshaped
  have frame := context_tail_any_return_frames_other_object raw notes volume sct volumeAvailable treeKey notesKey volumeKey payload entryKey dayKey nullifierKey
    context {child with cache := (TransferRawEffectsSource01.reshape (TransferWholeNullifierAdmission01.installedBackend raw notes volume sct volumeAvailable
      treeKey notesKey volumeKey payload entryKey context) wordMax capacity nullifierKey child (inputs action) (outputs action)).cache} notTree notVolume
  refine ⟨pending, inspected, ?_⟩
  rw [TransferWholeNullifierAdmission01.branch_is_exact_complete_item_capability_program,
    TransferCapabilitySource01.exact_rebinding_dispatches_projected_action _ extract inputs outputs wordMax capacity nullifierKey entryKey dayKey
      action ⟨item, context⟩ child extracted]
  simpa only [TransferCapabilitySource01.liftRaw, TransferRawEffectsSource01.executeTransfer, ↓reduceIte, next, reshaped] using frame.trans retained

theorem whole_delivery_success_retains_body_objects {O E A X : Type}
    (api : Api O E A) (keys : Keys) (codec : Codec) (index : Backend O E A) (body : Delta O E → Outcome O E X)
    (registryMatches exclusive : Bool) (mode : IndexMode) (action : A) (parent : State O) (queued : List A) (committed : Commit O E A)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi api keys codec index body) registryMatches exclusive mode action parent queued = some committed) :
    (body ⟨parent, empty⟩).result = .ok () ∧ committed.parent.objects = (applyCache parent (body ⟨parent, empty⟩).cache).objects := by
  obtain ⟨_, _, executed, prepared, performed, indexed, applied, _, _⟩ := successful_delivery_order _ registryMatches exclusive mode action parent queued committed success
  change asCache (body ⟨parent, empty⟩) = some executed at performed
  obtain ⟨bodySuccess, selected⟩ := TransferOrdinaryIndexDelivery01.selected_cache_derives_success _ executed performed
  subst executed
  refine ⟨bodySuccess, ?_⟩
  cases mode with
  | noIndex =>
    have same : ((⟨parent, (body ⟨parent, empty⟩).cache⟩ : Delta O E), (none : Option A)) = prepared := Option.some.inj indexed
    subst prepared
    exact congrArg State.objects applied
  | perTransaction =>
    exact (TransferOrdinaryIndexDelivery01.per_transaction_success_preserves_body_effect_domains api keys codec index body
      registryMatches exclusive action parent queued committed success).2.1
  | deferred =>
    cases heightRead : api.height ⟨parent, (body ⟨parent, empty⟩).cache⟩ with
    | none =>
      simp only [prepareIndex, TransferOrdinaryIndexDelivery01.combinedApi, indexApi, heightRead, Option.map_none] at indexed
      contradiction
    | some height =>
      have same : ((⟨parent, (body ⟨parent, empty⟩).cache⟩ : Delta O E), some action) = prepared :=
        Option.some.inj (by simpa only [prepareIndex, TransferOrdinaryIndexDelivery01.combinedApi, indexApi, heightRead, Option.map_some] using indexed)
      subst prepared
      exact congrArg State.objects applied

theorem whole_delivery_success_retains_bounded_fresh_pending_nullifier_encoding {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (convert : A → Option Encoded) (indexAvailable : Delta O E → Nat → Bool)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (mode : IndexMode) (parent : State O) (queued : List A) (committed : Commit O E A)
    (nonempty : (inputs action).isEmpty = false) (belowWord : capacity < wordMax)
    (notTree : nullifierKey ≠ treeKey) (notNotes : nullifierKey ≠ notesKey) (notVolume : nullifierKey ≠ volumeKey)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (TransferDeferredBodyFailure01.executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey
        volumeKey payload nullifierKey entryKey dayKey context action item)) registryMatches exclusive mode action parent queued = some committed) :
    ∃ pending : TransferNullifierBatchSource01.Pending,
      TransferNullifierBatchSource01.inspect raw.nullifiers wordMax capacity ⟨parent, empty⟩ (inputs action) = .ok pending ∧
      committed.parent.objects nullifierKey = some (raw.nullifiers.encode pending) ∧
      pending.ordered = (raw.nullifiers.pending ⟨parent, empty⟩).ordered ++ inputs action ∧ pending.ordered.length ≤ capacity ∧
      pending.sealed = false ∧ ∀ key ∈ inputs action, raw.nullifiers.lookup ⟨parent, empty⟩ key = some false ∧
        (raw.nullifiers.pending ⟨parent, empty⟩).membership key = false ∧ pending.membership key = true := by
  obtain ⟨bodySuccess, objects⟩ := whole_delivery_success_retains_body_objects api keys TransferIndexCountCodec01.codec
    (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable) _ registryMatches exclusive mode action parent queued committed success
  obtain ⟨pending, inspected, retained⟩ := successful_bound_body_retains_admitted_pending_object raw notes volume sct volumeAvailable extract inputs outputs
    wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item ⟨parent, empty⟩ nonempty notTree notNotes notVolume bodySuccess
  have admission := TransferNullifierBatchSource01.inspection_success_capacity_and_all_inputs raw.nullifiers wordMax capacity ⟨parent, empty⟩
    (inputs action) pending belowWord inspected
  refine ⟨pending, inspected, ?_, admission⟩
  rw [objects]
  change overlay parent.objects _ nullifierKey = some (raw.nullifiers.encode pending)
  simp only [overlay, retained]

set_option pp.all true in
#check @sct_any_return_frames_other_object
#print axioms sct_any_return_frames_other_object
set_option pp.all true in
#check @manager_any_return_frames_other_object
#print axioms manager_any_return_frames_other_object
set_option pp.all true in
#check @all_notes_any_return_frames_other_object
#print axioms all_notes_any_return_frames_other_object
set_option pp.all true in
#check @record_volume_any_return_preserves_objects
#print axioms record_volume_any_return_preserves_objects
set_option pp.all true in
#check @ordinary_volume_tail_any_return_frames_other_object
#print axioms ordinary_volume_tail_any_return_frames_other_object
set_option pp.all true in
#check @context_tail_any_return_frames_other_object
#print axioms context_tail_any_return_frames_other_object
set_option pp.all true in
#check @successful_reshape_retains_admitted_pending_object
#print axioms successful_reshape_retains_admitted_pending_object
set_option pp.all true in
#check @successful_context_reshape_retains_admitted_pending_object
#print axioms successful_context_reshape_retains_admitted_pending_object
set_option pp.all true in
#check @successful_bound_body_retains_admitted_pending_object
#print axioms successful_bound_body_retains_admitted_pending_object
set_option pp.all true in
#check @whole_delivery_success_retains_body_objects
#print axioms whole_delivery_success_retains_body_objects
set_option pp.all true in
#check @whole_delivery_success_retains_bounded_fresh_pending_nullifier_encoding
#print axioms whole_delivery_success_retains_bounded_fresh_pending_nullifier_encoding
end ShielddSecurity.TransferPendingNullifierRetention01
