import ShielddSecurity.TransferFeeFundingDelivery01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferDeferredBodyFailure01
open TransferStateDelta TransferRawStateProgram01 TransferIndexWriterModel01
open TransferVerificationEqualitySource01 (Item)

/-! Compose successful body delivery with deferred indexing failure. The
Ordinary and FeeFunding branches use their qualified exact-Item programs.
The queue is derived from delivery, and max-count bytes are supplied only
for the original parent. Failed flush preserves the delivered body effects;
it does not roll them back to the pre-delivery state. Empty same-instance
retry cannot reconstruct the consumed queue. Rust ownership, actual source
height/byte/key/token/crypto/Host/native/durability remain separate interfaces.
Earlier conversion/read/duplicate failures do not count as overflow controls. -/

def executeBound {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item) (child : Delta O E) :
    Outcome O E (TransferCapabilitySource01.Error K (TransferSctInsertionSource01.Error X)) :=
  match context with
  | .ordinary => TransferBoundOrdinarySource01.executeBound raw notes volume sct volumeAvailable extract inputs outputs
      wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey action item child
  | .feeFunding => TransferFeeFundingDelivery01.executeBound raw notes sct extract inputs outputs
      wordMax capacity treeKey notesKey nullifierKey entryKey dayKey action item child

theorem any_context_any_return_preserves_nonverifiable_writes {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item) (child : Delta O E) :
    (executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey volumeKey
      payload nullifierKey entryKey dayKey context action item child).cache.nonverifiable = child.cache.nonverifiable := by
  cases context with
  | ordinary =>
    exact TransferBoundOrdinarySource01.any_return_preserves_input_nonverifiable_writes raw notes volume sct
      volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey
      action item child
  | feeFunding =>
    exact (TransferFeeFundingDelivery01.any_return_preserves_verifiable_and_nonverifiable_writes raw notes sct
      extract inputs outputs wordMax capacity treeKey notesKey nullifierKey entryKey dayKey action item child).2

theorem deferred_success_derives_body_effects_exact_queue_and_original_nv {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (convert : A → Option Encoded) (indexAvailable : Delta O E → Nat → Bool)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (parent : State O) (queued : List A) (committed : Commit O E A)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey volumeKey
        payload nullifierKey entryKey dayKey context action item)) registryMatches exclusive .deferred action parent queued = some committed) :
    let body := executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey
      volumeKey payload nullifierKey entryKey dayKey context action item ⟨parent, empty⟩
    registryMatches = true ∧ exclusive = true ∧ extract action context = .ok item ∧ body.result = .ok () ∧
      (∃ deliveryHeight, api.height ⟨parent, body.cache⟩ = some deliveryHeight) ∧
      committed.parent = applyCache parent body.cache ∧ committed.events = body.cache.events ∧
      committed.deferred = queued ++ [action] ∧ committed.parent.nonverifiable = parent.nonverifiable := by
  dsimp only
  obtain ⟨registry, unique, executed, prepared, performed, indexed, applied, events, deferred⟩ :=
    successful_delivery_order _ registryMatches exclusive .deferred action parent queued committed success
  change asCache (executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey
    volumeKey payload nullifierKey entryKey dayKey context action item ⟨parent, empty⟩) = some executed at performed
  obtain ⟨bodySuccess, selected⟩ := TransferOrdinaryIndexDelivery01.selected_cache_derives_success _ executed performed
  subst executed
  cases heightRead : api.height ⟨parent, (executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity
      treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item ⟨parent, empty⟩).cache⟩ with
  | none =>
    simp only [prepareIndex, TransferOrdinaryIndexDelivery01.combinedApi, indexApi, heightRead, Option.map_none] at indexed
    contradiction
  | some deliveryHeight =>
    have same : ((⟨parent, (executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey
        volumeKey payload nullifierKey entryKey dayKey context action item ⟨parent, empty⟩).cache⟩ : Delta O E), some action) = prepared :=
      Option.some.inj (by simpa only [prepareIndex, TransferOrdinaryIndexDelivery01.combinedApi, indexApi, heightRead, Option.map_some] using indexed)
    subst prepared
    have extracted : extract action context = .ok item := by
      cases context with
      | ordinary =>
        exact (TransferBoundOrdinarySource01.successful_body_derives_reextraction_freshness_and_markers raw notes volume sct
          volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey
          action item ⟨parent, empty⟩ bodySuccess).1
      | feeFunding =>
        exact (TransferFeeFundingDelivery01.successful_body_derives_reextraction_and_actual_reshape raw notes sct
          extract inputs outputs wordMax capacity treeKey notesKey nullifierKey entryKey dayKey action item ⟨parent, empty⟩ bodySuccess).1
    refine ⟨registry, unique, extracted, bodySuccess, ⟨deliveryHeight, rfl⟩, applied, events, ?_, ?_⟩
    · simpa only [Option.toList_some] using deferred
    · rw [applied]
      change overlay parent.nonverifiable _ = parent.nonverifiable
      rw [any_context_any_return_preserves_nonverifiable_writes raw notes volume sct volumeAvailable extract inputs outputs
        wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey context action item ⟨parent, empty⟩]
      rfl

theorem delivered_body_then_max_count_flush_failure_preserves_delivered_effects_and_empty_retry {O E K X Tree A : Type}
    (api : Api O E A) (keys : Keys) (convert : A → Option Encoded) (indexAvailable : Delta O E → Nat → Bool)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree) (volumeAvailable : Delta O E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey flushHeight : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item)
    (registryMatches exclusive : Bool) (parent : State O) (queued : List A) (committed : Commit O E A)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi api keys TransferIndexCountCodec01.codec
      (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey volumeKey
        payload nullifierKey entryKey dayKey context action item)) registryMatches exclusive .deferred action parent queued = some committed)
    (storedCount : parent.nonverifiable (keys.count flushHeight) = some TransferOrdinaryMaxCount01.maxBytes)
    (retryPut : TransferDeferredQueueSourceModel01.IndexWriter O E A IndexError)
    (retryExclusive : Bool) (retryHeight : Option Nat) :
    let body := executeBound raw notes volume sct volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey
      volumeKey payload nullifierKey entryKey dayKey context action item ⟨parent, empty⟩
    let interrupted := TransferDeferredQueueSourceModel01.flush
      (TransferDeferredCountWalk01.queueWriter (E := E) keys convert indexAvailable committed.parent)
      true true (some flushHeight) committed.parent committed.deferred
    extract action context = .ok item ∧ body.result = .ok () ∧
      committed.parent = applyCache parent body.cache ∧ committed.events = body.cache.events ∧
      committed.deferred = queued ++ [action] ∧
      (∃ error : IndexError, interrupted = TransferDeferredQueueSourceModel01.refused committed.parent [] (.index error)) ∧
      TransferDeferredQueueSourceModel01.flush retryPut true retryExclusive retryHeight interrupted.parent interrupted.queued =
        TransferDeferredQueueSourceModel01.unchanged committed.parent [] := by
  dsimp only
  obtain ⟨_, _, extracted, bodySuccess, _, applied, events, deferred, nv⟩ :=
    deferred_success_derives_body_effects_exact_queue_and_original_nv api keys convert indexAvailable raw notes volume sct
      volumeAvailable extract inputs outputs wordMax capacity treeKey notesKey volumeKey payload nullifierKey entryKey dayKey
      context action item registryMatches exclusive parent queued committed success
  have nonempty : committed.deferred ≠ [] := by
    rw [deferred]
    intro emptyQueue
    have lengths := congrArg List.length emptyQueue
    simp only [List.length_append, List.length_singleton, List.length_nil] at lengths
    omega
  have count : committed.parent.nonverifiable (keys.count flushHeight) = some TransferOrdinaryMaxCount01.maxBytes := by
    rw [nv]
    exact storedCount
  exact ⟨extracted, bodySuccess, applied, events, deferred,
    TransferDeferredMaxCount01.max_count_flush_derives_failure_parent_and_drained_queue (E := E)
      keys convert indexAvailable flushHeight committed.parent committed.deferred nonempty count,
    TransferDeferredMaxCount01.max_count_same_instance_retry_cannot_reconstruct_queue
      keys convert indexAvailable flushHeight committed.parent committed.deferred nonempty count retryPut retryExclusive retryHeight⟩

set_option pp.all true in
#check @executeBound
#print axioms executeBound
set_option pp.all true in
#check @any_context_any_return_preserves_nonverifiable_writes
#print axioms any_context_any_return_preserves_nonverifiable_writes
set_option pp.all true in
#check @deferred_success_derives_body_effects_exact_queue_and_original_nv
#print axioms deferred_success_derives_body_effects_exact_queue_and_original_nv
set_option pp.all true in
#check @delivered_body_then_max_count_flush_failure_preserves_delivered_effects_and_empty_retry
#print axioms delivered_body_then_max_count_flush_failure_preserves_delivered_effects_and_empty_retry
end ShielddSecurity.TransferDeferredBodyFailure01
