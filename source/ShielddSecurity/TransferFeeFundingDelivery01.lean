import ShielddSecurity.TransferDeferredMaxCount01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferFeeFundingDelivery01
open TransferStateDelta TransferRawStateProgram01 TransferIndexWriterModel01
open TransferVerificationEqualitySource01 (Item)

/-! FeeFunding re-extracts the same action before its installed nullifier/note
program. It skips the ordinary volume tail. Whole per-transaction success
derives exact current reads, decodable index values and original V storage;
it retains the actual note/object/events rather than assuming their success.
Rust extractor/token/crypto/key/byte/store/ownership/Host/native/durability
correspondence remains separate. No native or negative-control credit. -/

def executeBound {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) (child : Delta O E) :
    Outcome O E (TransferCapabilitySource01.Error K (TransferSctInsertionSource01.Error X)) :=
  TransferCapabilitySource01.execute (TransferRawSourceFrames01.installNotes raw notes sct treeKey notesKey)
    extract inputs outputs wordMax capacity nullifierKey entryKey dayKey action ⟨item, .feeFunding⟩ child

theorem any_return_preserves_verifiable_and_nonverifiable_writes {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) (child : Delta O E) :
    (executeBound raw notes sct extract inputs outputs wordMax capacity treeKey notesKey nullifierKey entryKey dayKey
      action item child).cache.verifiable = child.cache.verifiable ∧
    (executeBound raw notes sct extract inputs outputs wordMax capacity treeKey notesKey nullifierKey entryKey dayKey
      action item child).cache.nonverifiable = child.cache.nonverifiable := by
  cases observed : extract action .feeFunding with
  | error error => simp only [executeBound, TransferCapabilitySource01.execute, observed]; exact ⟨True.intro, True.intro⟩
  | ok current =>
    by_cases matched : current = item
    · simpa only [executeBound, TransferCapabilitySource01.execute, observed, if_pos matched,
        TransferCapabilitySource01.liftRaw, TransferCapabilitySource01.isOrdinary] using
        TransferRawSourceFrames01.fee_funding_preserves_input_write_domains_on_any_return raw notes sct
          wordMax capacity treeKey notesKey nullifierKey entryKey dayKey true child (inputs action) (outputs action)
    · simp only [executeBound, TransferCapabilitySource01.execute, observed, if_neg matched]; exact ⟨True.intro, True.intro⟩

theorem successful_body_derives_reextraction_and_actual_reshape {O E K X Tree A : Type}
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) (child : Delta O E)
    (success : (executeBound raw notes sct extract inputs outputs wordMax capacity treeKey notesKey nullifierKey
      entryKey dayKey action item child).result = .ok ()) :
    extract action .feeFunding = .ok item ∧
      (TransferRawEffectsSource01.reshape (TransferRawSourceFrames01.installNotes raw notes sct treeKey notesKey)
        wordMax capacity nullifierKey child (inputs action) (outputs action)).result = .ok () ∧
      (executeBound raw notes sct extract inputs outputs wordMax capacity treeKey notesKey nullifierKey entryKey dayKey
        action item child).cache =
      (TransferRawEffectsSource01.reshape (TransferRawSourceFrames01.installNotes raw notes sct treeKey notesKey)
        wordMax capacity nullifierKey child (inputs action) (outputs action)).cache := by
  have extracted := TransferCapabilitySource01.successful_execution_derives_exact_reextraction
    (TransferRawSourceFrames01.installNotes raw notes sct treeKey notesKey) extract inputs outputs
    wordMax capacity nullifierKey entryKey dayKey action ⟨item, .feeFunding⟩ child success
  have dispatch := TransferCapabilitySource01.exact_rebinding_dispatches_projected_action
    (TransferRawSourceFrames01.installNotes raw notes sct treeKey notesKey) extract inputs outputs
    wordMax capacity nullifierKey entryKey dayKey action ⟨item, .feeFunding⟩ child extracted
  change executeBound raw notes sct extract inputs outputs wordMax capacity treeKey notesKey nullifierKey entryKey dayKey
    action item child = _ at dispatch
  cases result : (TransferRawEffectsSource01.reshape (TransferRawSourceFrames01.installNotes raw notes sct treeKey notesKey)
      wordMax capacity nullifierKey child (inputs action) (outputs action)).result with
  | error error =>
    simp only [dispatch, TransferRawEffectsSource01.executeTransfer,
      ↓reduceIte, next, result, TransferCapabilitySource01.liftRaw] at success
    contradiction
  | ok returnedUnit =>
    cases returnedUnit
    refine ⟨extracted, rfl, ?_⟩
    simp only [dispatch, TransferCapabilitySource01.isOrdinary, TransferRawEffectsSource01.executeTransfer,
      ↓reduceIte, next, result, TransferRawEffectsSource01.fee_funding_skips_volume_tail,
      TransferCapabilitySource01.liftRaw]

theorem whole_success_derives_original_reads_decodable_index_and_retained_effects {O E K X Tree A : Type}
    (api : Api O E A) (project : Bytes → Nat) (injection : Function.Injective project) (prefixBytes : Nat → Bytes)
    (convert : A → Option Encoded) (indexAvailable : Delta O E → Nat → Bool)
    (raw : TransferRawEffectsSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (notes : TransferNoteManagerSource01.Backend O E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend O E X Tree)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity treeKey notesKey nullifierKey entryKey dayKey : Nat)
    (action : A) (item : Item) (registryMatches exclusive : Bool) (parent : State O)
    (queued : List A) (committed : Commit O E A)
    (success : run (TransferOrdinaryIndexDelivery01.combinedApi api
      (TransferIndexInspectionFacts01.keysFromBytes project prefixBytes (TransferIndexCountCodec01.encodeBE 8))
      TransferIndexCountCodec01.codec (TransferOrdinaryIndexReadSource01.installReads convert indexAvailable)
      (executeBound raw notes sct extract inputs outputs wordMax capacity treeKey notesKey nullifierKey entryKey dayKey action item))
      registryMatches exclusive .perTransaction action parent queued = some committed) :
    let keys := TransferIndexInspectionFacts01.keysFromBytes project prefixBytes (TransferIndexCountCodec01.encodeBE 8)
    let body := executeBound raw notes sct extract inputs outputs wordMax capacity treeKey notesKey nullifierKey entryKey dayKey
      action item ⟨parent, empty⟩
    registryMatches = true ∧ exclusive = true ∧
    ∃ (height : Nat) (witness : Witness),
      extract action .feeFunding = .ok item ∧ convert action = some witness.encoded ∧
      parent.nonverifiable (keys.identifier height witness.encoded.identifier) = none ∧
      countObservation TransferIndexCountCodec01.codec (parent.nonverifiable (keys.count height)) = some witness.ordinal ∧
      witness.next.val = witness.ordinal.val + 1 ∧ witness.ordinal.val + 1 < 2 ^ 64 ∧
      committed.parent.verifiable = parent.verifiable ∧
      committed.parent.objects = (applyCache parent body.cache).objects ∧ committed.events = body.cache.events ∧
      committed.parent.nonverifiable (keys.entry height witness.ordinal.val) = some witness.encoded.payload ∧
      committed.parent.nonverifiable (keys.identifier height witness.encoded.identifier) =
        some (TransferIndexCountCodec01.codec.encodeCount witness.ordinal) ∧
      committed.parent.nonverifiable (keys.count height) = some (TransferIndexCountCodec01.codec.encodeCount witness.next) ∧
      TransferIndexCountCodec01.codec.decodeCount (TransferIndexCountCodec01.codec.encodeCount witness.ordinal) = some witness.ordinal ∧
      TransferIndexCountCodec01.codec.decodeCount (TransferIndexCountCodec01.codec.encodeCount witness.next) = some witness.next ∧
      committed.deferred = queued := by
  dsimp only
  obtain ⟨registry, unique, height, witness, bodySuccess, _, inspected, applied, events, deferred⟩ :=
    TransferOrdinaryIndexDelivery01.per_transaction_success_recovers_body_height_and_index _ _ _ _ _
      registryMatches exclusive action parent queued committed success
  have bound := successful_body_derives_reextraction_and_actual_reshape raw notes sct extract inputs outputs wordMax capacity
    treeKey notesKey nullifierKey entryKey dayKey action item ⟨parent, empty⟩ bodySuccess
  have frame := any_return_preserves_verifiable_and_nonverifiable_writes raw notes sct extract inputs outputs wordMax capacity
    treeKey notesKey nullifierKey entryKey dayKey action item ⟨parent, empty⟩
  obtain ⟨countValue, converted, absent, countRead, decoded, _⟩ := TransferIndexInspectionFacts01.inspect_success_order
    _ _ _ height action _ witness inspected
  have idRead := TransferOrdinaryIndexReadSource01.successful_nv_read_derives_available_current_value
    indexAvailable _ _ none absent
  have observedCount := TransferOrdinaryIndexReadSource01.successful_nv_read_derives_available_current_value
    indexAvailable _ _ countValue countRead
  have currentNv : (applyCache parent (executeBound raw notes sct extract inputs outputs wordMax capacity treeKey notesKey
      nullifierKey entryKey dayKey action item ⟨parent, empty⟩).cache).nonverifiable = parent.nonverifiable := by
    change overlay parent.nonverifiable _ = parent.nonverifiable
    rw [frame.2]
    rfl
  obtain ⟨increment, bounded⟩ := TransferIndexInspectionFacts01.inspect_success_checked_increment _ _ _ height action _ witness inspected
  obtain ⟨entryCount, idCount, entryId⟩ := TransferIndexInspectionFacts01.projected_keys_separate
    project injection prefixBytes (TransferIndexCountCodec01.encodeBE 8) height witness.ordinal.val witness.encoded.identifier
  refine ⟨registry, unique, height, witness, bound.1, converted, ?_, ?_, increment, bounded, ?_, ?_, events,
    ?_, ?_, ?_, TransferIndexCountCodec01.codec_roundtrip witness.ordinal,
    TransferIndexCountCodec01.codec_roundtrip witness.next, deferred⟩
  · rw [currentNv] at idRead; exact idRead.2
  · rw [currentNv] at observedCount; rw [observedCount.2]; exact decoded
  · rw [applied]
    change overlay parent.verifiable _ = parent.verifiable
    rw [(writeIndex_frames _ _ height witness _).1, frame.1]
    rfl
  · rw [applied]; rfl
  · rw [applied]
    simp only [applyCache, overlay, TransferIndexInspectionFacts01.writeIndex_entry _ _ height witness _ entryCount entryId]
  · rw [applied]
    simp only [applyCache, overlay, TransferIndexInspectionFacts01.writeIndex_identifier _ _ height witness _ idCount]
  · rw [applied]
    simp only [applyCache, overlay, writeIndex_count]

set_option pp.all true in
#check @executeBound
#print axioms executeBound
set_option pp.all true in
#check @any_return_preserves_verifiable_and_nonverifiable_writes
#print axioms any_return_preserves_verifiable_and_nonverifiable_writes
set_option pp.all true in
#check @successful_body_derives_reextraction_and_actual_reshape
#print axioms successful_body_derives_reextraction_and_actual_reshape
set_option pp.all true in
#check @whole_success_derives_original_reads_decodable_index_and_retained_effects
#print axioms whole_success_derives_original_reads_decodable_index_and_retained_effects
end ShielddSecurity.TransferFeeFundingDelivery01
