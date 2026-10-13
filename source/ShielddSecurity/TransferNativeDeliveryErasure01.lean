import ShielddSecurity.TransferNativeGhostErasure01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferNativeDeliveryErasure01
open TransferStateDelta TransferRawStateProgram01
open TransferPendingFiniteCodec01 (NativePending)
open TransferPendingSetInvariant01 (Invariant)
open TransferBoundedNativeCodec01 (ExtendedObject BoundedPending nullifierModulus)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferNativeRawPending01 (nativeRaw)
open TransferNativeGhostErasure01 (nativeOnlyRaw)
open TransferVerificationEqualitySource01 (Item)

/-! Lift accepted bounded primitive/raw ghost erasure through exact complete
Item re-extraction, installed source note/volume/SCT branches and enclosing
delivery/index selection. Equality includes returned body errors, which the
delivery adapter discards, as well as exact successful parent/events/queue.
Identical source observations and callbacks are reused, without a desired
success or poststate premise. This remains source-model equality, not native
Rust codec/getter/input/callback/trace/ownership/OS refinement. -/

theorem bounded_capability_ghost_erasure_preserves_every_returned_outcome {O E K X A I : Type} [DecidableEq I]
    (encodeNative : NativePending → O) (raw : TransferRawEffectsSource01.Backend (ExtendedObject O) E X)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K I) (inputs outputs : A → List Nat)
    (wordMax pendingKey entryKey dayKey : Nat) (action : A) (token : TransferCapabilitySource01.Validated I)
    (child : Delta (ExtendedObject O) E)
    (initial : Invariant blockCapacity (raw.nullifiers.pending child))
    (bounded : BoundedPending (raw.nullifiers.pending child))
    (nativeInputs : ∀ key ∈ inputs action, key < nullifierModulus) (belowWord : blockCapacity < wordMax) :
    TransferCapabilitySource01.execute (nativeRaw encodeNative raw) extract inputs outputs wordMax blockCapacity
      pendingKey entryKey dayKey action token child =
      TransferCapabilitySource01.execute (nativeOnlyRaw encodeNative raw) extract inputs outputs wordMax blockCapacity
        pendingKey entryKey dayKey action token child := by
  have rawEqual := TransferNativeGhostErasure01.bounded_raw_transfer_ghost_erasure_preserves_every_returned_outcome
    encodeNative raw wordMax pendingKey entryKey dayKey true (TransferCapabilitySource01.isOrdinary token.context)
    child (inputs action) (outputs action) initial bounded nativeInputs belowWord
  simp only [TransferCapabilitySource01.execute, rawEqual]

theorem source_callback_installation_commutes_with_both_pending_encoders {O E X Tree : Type}
    (encodeNative : NativePending → O)
    (raw : TransferRawEffectsSource01.Backend (ExtendedObject O) E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend (ExtendedObject O) E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend (ExtendedObject O) E X Tree) (volumeAvailable : Delta (ExtendedObject O) E → Bool)
    (treeKey notesKey volumeKey payload entryKey : Nat) (context : TransferCapabilitySource01.ProofContext) :
    TransferWholeNullifierAdmission01.installedBackend (nativeRaw encodeNative raw) notes volume sct volumeAvailable treeKey notesKey volumeKey payload entryKey context =
      nativeRaw encodeNative (TransferWholeNullifierAdmission01.installedBackend raw notes volume sct volumeAvailable treeKey notesKey volumeKey payload entryKey context) ∧
    TransferWholeNullifierAdmission01.installedBackend (nativeOnlyRaw encodeNative raw) notes volume sct volumeAvailable treeKey notesKey volumeKey payload entryKey context =
      nativeOnlyRaw encodeNative (TransferWholeNullifierAdmission01.installedBackend raw notes volume sct volumeAvailable treeKey notesKey volumeKey payload entryKey context) := by
  cases context <;> exact ⟨rfl, rfl⟩

theorem bounded_complete_item_body_ghost_erasure_preserves_every_returned_outcome {O E K X Tree A : Type}
    (encodeNative : NativePending → O)
    (raw : TransferRawEffectsSource01.Backend (ExtendedObject O) E (TransferSctInsertionSource01.Error X))
    (notes volume : TransferNoteManagerSource01.Backend (ExtendedObject O) E (TransferSctInsertionSource01.Error X))
    (sct : TransferSctInsertionSource01.Backend (ExtendedObject O) E X Tree) (volumeAvailable : Delta (ExtendedObject O) E → Bool)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax treeKey notesKey volumeKey payload pendingKey entryKey dayKey : Nat)
    (context : TransferCapabilitySource01.ProofContext) (action : A) (item : Item) (child : Delta (ExtendedObject O) E)
    (initial : Invariant blockCapacity (raw.nullifiers.pending child))
    (bounded : BoundedPending (raw.nullifiers.pending child))
    (nativeInputs : ∀ key ∈ inputs action, key < nullifierModulus) (belowWord : blockCapacity < wordMax) :
    TransferDeferredBodyFailure01.executeBound (nativeRaw encodeNative raw) notes volume sct volumeAvailable extract inputs outputs
      wordMax blockCapacity treeKey notesKey volumeKey payload pendingKey entryKey dayKey context action item child =
      TransferDeferredBodyFailure01.executeBound (nativeOnlyRaw encodeNative raw) notes volume sct volumeAvailable extract inputs outputs
        wordMax blockCapacity treeKey notesKey volumeKey payload pendingKey entryKey dayKey context action item child := by
  rw [TransferWholeNullifierAdmission01.branch_is_exact_complete_item_capability_program,
    TransferWholeNullifierAdmission01.branch_is_exact_complete_item_capability_program]
  have installed := source_callback_installation_commutes_with_both_pending_encoders
    encodeNative raw notes volume sct volumeAvailable treeKey notesKey volumeKey payload entryKey context
  rw [installed.1, installed.2]
  have retained := (TransferWholeNullifierAdmission01.installed_backend_retains_original_source_and_nullifiers
    raw notes volume sct volumeAvailable treeKey notesKey volumeKey payload entryKey context).2
  exact bounded_capability_ghost_erasure_preserves_every_returned_outcome encodeNative
    (TransferWholeNullifierAdmission01.installedBackend raw notes volume sct volumeAvailable treeKey notesKey volumeKey payload entryKey context)
    extract inputs outputs wordMax pendingKey entryKey dayKey action ⟨item, context⟩ child
    (by rw [retained]; exact initial) (by rw [retained]; exact bounded) nativeInputs belowWord

theorem pointwise_body_equality_derives_exact_delivery_all_index_modes {O E A X : Type}
    (api : Api O E A) (keys : TransferIndexWriterModel01.Keys) (codec : TransferIndexWriterModel01.Codec)
    (index : TransferIndexWriterModel01.Backend O E A) (first second : Delta O E → Outcome O E X)
    (registryMatches exclusive : Bool) (mode : IndexMode) (action : A) (parent : State O) (queued : List A)
    (same : first ⟨parent, empty⟩ = second ⟨parent, empty⟩) :
    run (TransferOrdinaryIndexDelivery01.combinedApi api keys codec index first) registryMatches exclusive mode action parent queued =
      run (TransferOrdinaryIndexDelivery01.combinedApi api keys codec index second) registryMatches exclusive mode action parent queued := by
  cases registryMatches with
  | false => rfl
  | true =>
    cases exclusive with
    | false => rfl
    | true =>
      simp only [run, begin, if_true, Option.bind_some, TransferOrdinaryIndexDelivery01.combinedApi]
      rw [same]
      rfl

set_option pp.all true in
#check @bounded_capability_ghost_erasure_preserves_every_returned_outcome
#print axioms bounded_capability_ghost_erasure_preserves_every_returned_outcome
set_option pp.all true in
#check @source_callback_installation_commutes_with_both_pending_encoders
#print axioms source_callback_installation_commutes_with_both_pending_encoders
set_option pp.all true in
#check @bounded_complete_item_body_ghost_erasure_preserves_every_returned_outcome
#print axioms bounded_complete_item_body_ghost_erasure_preserves_every_returned_outcome
set_option pp.all true in
#check @pointwise_body_equality_derives_exact_delivery_all_index_modes
#print axioms pointwise_body_equality_derives_exact_delivery_all_index_modes
end ShielddSecurity.TransferNativeDeliveryErasure01
