import ShielddSecurity.TransferTaggedCodecPublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferAbsentStartPublication01
open TransferStateDelta
open TransferPendingFiniteCodec01 (NativePending restore)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject decodeObject nativeSupported nullifierModulus)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBlockPendingSequence01 (Request allInputs)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferSourceTypedInputProjection01 (typedWords installTypedInputs)
open TransferKnownFinalizerPublication01 (Effects installIo)
open TransferInstalledSourcePublication01 (SourceRequest installRequests)
open TransferInjectiveKeyPublication01 (keyCode)
open TransferFinalizationObjectFrames01 (Mutation)
open TransferFixedFinalizerPublication01 (FinalizationWrites installFixedIo)
open TransferPendingSetInvariant01 (Invariant)
open TransferBoundedNativeCodec01 (BoundedPending)
open TransferBlockPendingSequence01 (parentPending)
open TransferNativeGetterPublication01 (installGetterIo)
open TransferTaggedCodecPublication01 (TaggedObject encodePending decodePending OtherFinalizationWrites liftWrites installTaggedIo)
open TransferBlockPendingSequence01 (step walk)
/-! Initial absent pending cache reads as default empty pending. Generic bounded
walk induction needs no initial stored object; nil preserves absence until
the concrete finalizer seals the empty vector. Fresh-parent constructor gives
an absent pending slot while retaining V/NV and other object observations.
Whole tagged source publication derives the exact mathematical vector and
physical boundary without caller stored-empty-object/codec/getter/frame/key
proofs. Native fresh snapshot/cache constructor, Any/Clone/selectors/full
trace/ownership/OS correspondence remains explicit; source model only. -/

def freshParent {O : Type} (verifiable nonverifiable : View Bytes) (otherObjects : View O) : State O :=
  ⟨verifiable, nonverifiable, fun key => if key = keyCode TransferNullifierObjectKeys01.nullifierBytes then none else otherObjects key⟩

theorem symbolic_bounded_walk_preserves_invariant_and_domain_without_initial_object {O E K X Tree A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (requests : List (Request (ExtendedObject O) E K X Tree A))
    (parent : State (ExtendedObject O)) (queued : List A) (final : State (ExtendedObject O) × List A)
    (initial : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent))
    (bounded : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent))
    (nativeInputs : ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus)
    (success : walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final) :
    Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project final.1) ∧
      BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project final.1) := by
  induction requests generalizing parent queued with
  | nil =>
    have same : (parent, queued) = final := Option.some.inj success
    subst final
    exact ⟨initial, bounded⟩
  | cons request rest ih =>
    cases first : step (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
        (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project request parent queued with
    | none => simp only [walk, first, Option.bind_none] at success; cases success
    | some committed =>
      have suffix : walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
          (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project committed.parent committed.deferred rest = some final := by
        simpa only [walk, first, Option.bind_some] using success
      obtain ⟨nextInvariant, nextBounded, _⟩ := TransferBoundedNativeCodec01.successful_bounded_whole_step_stores_supported_native_pending
        encodeNative decodeNative supportedRoundtrip project injection request parent queued committed initial bounded
        (nativeInputs request (by simp)) first
      exact ih committed.parent committed.deferred nextInvariant nextBounded
        (fun later inside => nativeInputs later (List.mem_cons_of_mem request inside)) suffix

theorem whole_absent_native_default_block_publishes_exact_global_native_sealed_inputs {O E K X Tree A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (requests : List (Request (ExtendedObject O) E K X Tree A))
    (parent : State (ExtendedObject O)) (queued : List A) (final : State (ExtendedObject O) × List A)
    (absent : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) = none)
    (nativeInputs : ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus)
    (walkedNative : TransferBlockPendingSequence01.walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final)
    (io : TransferEndToEnd01.Io (ExtendedObject O) E A) (host : TransferHostSealedCommit01.Host (ExtendedObject O))
    (height : Fin (2 ^ 64)) (root : Nat) (currentState : host.active = final.1)
    (projectedKeys : io.ending.project = project)
    (typedGetter : io.ending.decodePending (.inl (encodeNative (.sealed (allInputs requests)))) = restore (.sealed (allInputs requests)))
    (finalization : (TransferHostEndBlock01.finalized io.ending host height final.2).state.objects (io.ending.project TransferNullifierObjectKeys01.nullifierBytes) =
      (TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
        (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.ending.project host.active).objects (io.ending.project TransferNullifierObjectKeys01.nullifierBytes))
    (success : (TransferEndToEnd01.execute io host height final.2).root = some root) :
    ∃ state,
      (TransferHostEndBlock01.transferred io.ending host height final.2).returned = some state ∧
      state.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (.inl (encodeNative (.sealed (allInputs requests)))) ∧
      (allInputs requests).Nodup ∧ (allInputs requests).length ≤ blockCapacity ∧
      (∀ key ∈ allInputs requests, key < nullifierModulus) ∧
      ∃ (frozen : TransferWriterPrepareSource01.Frozen), frozen.insertions.accepted = allInputs requests ∧ frozen.next.applicationRoot = some root ∧
        (TransferEndToEnd01.execute io host height final.2).host.writer = .ready frozen.next ∧
        (TransferEndToEnd01.execute io host height final.2).host.phase = .idle ∧
        (TransferEndToEnd01.execute io host height final.2).host.store.actualRoots = frozen.next.nullifiers.roots ∧
        (TransferEndToEnd01.execute io host height final.2).host.store.boundary = some frozen.next.nullifiers := by
  have emptyBounded : BoundedPending TransferCurrentPendingReplay01.emptyPending := by
    intro key inside
    cases inside
  have totalRoundtrip0 := TransferBoundedNativeCodec01.restricted_native_roundtrip_totalizes_only_with_separate_unsupported_ghosts encodeNative decodeNative supportedRoundtrip
  have coherentRoundtrip0 := TransferPendingFiniteCodec01.typed_finite_codec_restores_coherent_pending
    (encodeObject encodeNative) (decodeObject decodeNative) totalRoundtrip0
  have emptyRead0 : parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent = TransferCurrentPendingReplay01.emptyPending :=
    TransferCurrentPendingReplay01.current_object_absence_derives_default
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) (project TransferNullifierObjectKeys01.nullifierBytes)
      ⟨parent, (empty : Cache (ExtendedObject O) Unit)⟩ (by simpa only [apply_empty] using absent)
  have initial0 : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent) := by
    rw [emptyRead0]
    exact TransferPendingSetInvariant01.empty_pending_invariant blockCapacity
  have bounded0 : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent) := by
    rw [emptyRead0]
    exact emptyBounded
  have erasedWalk := TransferNativeReachableErasure01.bounded_reachable_block_walk_erases_unsupported_encoder_ghosts
    encodeNative decodeNative supportedRoundtrip project injection requests parent queued initial0 bounded0 nativeInputs
  have walked : walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final := erasedWalk.trans walkedNative
  have nativeFinal := symbolic_bounded_walk_preserves_invariant_and_domain_without_initial_object
    encodeNative decodeNative supportedRoundtrip project injection requests parent queued final initial0 bounded0 nativeInputs walked
  have order := TransferReachablePendingBlock01.empty_start_reachable_walk_derives_global_inputs
    (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
    coherentRoundtrip0 project injection requests parent queued final emptyRead0 walked
  obtain ⟨_, _, _, _, state, frozen, _, _, taken, accepted, _, _, appRoot, _, _, _, _, idle, _, ready, _, _, roots, stored, _⟩ :=
    TransferEndToEnd01.whole_returned_pipeline_derives_exact_inputs_same_boundary_and_actual_physical_recovery io host height final.2 root success
  have initial : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.ending.project host.active) := by
    rw [projectedKeys, currentState]; exact nativeFinal.1
  have bounded : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.ending.project host.active) := by
    rw [projectedKeys, currentState]; exact nativeFinal.2
  have actualObject := TransferNativeSealTransfer01.actual_finalization_transfer_preserves_supported_native_sealed_pending_object
    encodeNative decodeNative io.ending host height final.2 initial bounded finalization state taken
  rw [projectedKeys, currentState, order.2.1] at actualObject
  have keyBounds := TransferBoundedNativeCodec01.bounded_whole_input_vector_from_native_action_projections requests nativeInputs
  have exactTakenInputs : (parentPending io.ending.decodePending io.ending.project state).ordered = allInputs requests := by
    simp only [parentPending, TransferCurrentPendingReplay01.currentPending, apply_empty, projectedKeys, actualObject,
      typedGetter, restore]
  have exactAccepted : frozen.insertions.accepted = allInputs requests := accepted.trans exactTakenInputs
  exact ⟨state, taken, actualObject, order.2.2.1, order.2.2.2.1, keyBounds, frozen, exactAccepted, appRoot, ready, idle, roots, stored⟩

theorem fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector {Other E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject (TaggedObject Other)) E K X Tree A I inputs))
    (verifiable nonverifiable : View Bytes) (otherObjects : View (ExtendedObject (TaggedObject Other))) (queued : List A) (final : State (ExtendedObject (TaggedObject Other)) × List A)
    (walkedNative : TransferBlockPendingSequence01.walk (TransferNativeReachableErasure01.nativeOnlyEncode encodePending)
      (TransferPendingFiniteCodec01.decode (decodeObject decodePending)) keyCode (freshParent verifiable nonverifiable otherObjects) queued (installRequests inputs wordOf sourceRequests) = some final)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (TaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (TaggedObject Other)) E A) (host : TransferHostSealedCommit01.Host (ExtendedObject (TaggedObject Other)))
    (height : Fin (2 ^ 64)) (root : Nat) (currentState : host.active = final.1)
    (success : (TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) host height final.2).root = some root) :
    allInputs (installRequests inputs wordOf sourceRequests) = (sourceRequests.flatMap (fun request => typedWords inputs wordOf request.base.action)).map montgomeryValue ∧
    ∃ state,
      (TransferHostEndBlock01.transferred (installTaggedIo writesOf baseIo).ending host height final.2).returned = some state ∧
      state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) = some (.inl (encodePending (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) ∧
      (allInputs (installRequests inputs wordOf sourceRequests)).Nodup ∧ (allInputs (installRequests inputs wordOf sourceRequests)).length ≤ blockCapacity ∧
      (∀ key ∈ allInputs (installRequests inputs wordOf sourceRequests), key < nullifierModulus) ∧
      ∃ (frozen : TransferWriterPrepareSource01.Frozen), frozen.insertions.accepted = allInputs (installRequests inputs wordOf sourceRequests) ∧ frozen.next.applicationRoot = some root ∧
        (TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) host height final.2).host.writer = .ready frozen.next ∧
        (TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) host height final.2).host.phase = .idle ∧
        (TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) host height final.2).host.store.actualRoots = frozen.next.nullifiers.roots ∧
        (TransferEndToEnd01.execute (installTaggedIo writesOf baseIo) host height final.2).host.store.boundary = some frozen.next.nullifiers := by
  let requests := installRequests inputs wordOf sourceRequests
  let parent := freshParent verifiable nonverifiable otherObjects
  let io := installTaggedIo writesOf baseIo
  have sourceProjection := TransferInstalledSourcePublication01.installed_request_batch_derives_every_source_projection inputs wordOf sourceRequests
  have nativeInputs := TransferTypedScalarPublication01.typed_action_projection_derives_canonical_native_input_bounds
    requests (fun request => typedWords inputs wordOf request.action) sourceProjection
  have absent : parent.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) = none := by
    simp only [parent, freshParent, ite_true]
  have getter : io.ending.decodePending (.inl (encodePending (.sealed (allInputs requests)))) = restore (.sealed (allInputs requests)) := rfl
  have frame := TransferKnownFinalizerPublication01.installed_known_finalizer_derives_reached_publication_field_frame
    (encodePending (Other := Other)) (decodePending (Other := Other)) keyCode TransferInjectiveKeyPublication01.keyCode_is_injective
    (fun height state queued => TransferFixedFinalizerPublication01.toEffects (liftWrites (writesOf height state queued)))
    {baseIo with ending := {baseIo.ending with decodePending := TransferPendingFiniteCodec01.decode (decodeObject decodePending)}}
    host height final.2
  have values := TransferTypedScalarPublication01.global_source_input_vector_is_exact_typed_montgomery_projection
    requests (fun request => typedWords inputs wordOf request.action) sourceProjection
  refine ⟨values.trans ?_, ?_⟩
  · exact congrArg (fun words : List (Vector UInt64 4) => words.map montgomeryValue)
      (TransferInstalledSourcePublication01.installed_request_batch_retains_exact_ordered_source_word_vector inputs wordOf sourceRequests)
  · exact whole_absent_native_default_block_publishes_exact_global_native_sealed_inputs
      (encodePending (Other := Other)) (decodePending (Other := Other))
      (fun native _ => TransferTaggedCodecPublication01.tagged_pending_restore_roundtrip native)
      keyCode TransferInjectiveKeyPublication01.keyCode_is_injective requests parent queued final absent nativeInputs walkedNative
      io host height root currentState rfl getter frame success
set_option pp.all true in
#check @freshParent
#print axioms freshParent
set_option pp.all true in
#check @symbolic_bounded_walk_preserves_invariant_and_domain_without_initial_object
#print axioms symbolic_bounded_walk_preserves_invariant_and_domain_without_initial_object
set_option pp.all true in
#check @whole_absent_native_default_block_publishes_exact_global_native_sealed_inputs
#print axioms whole_absent_native_default_block_publishes_exact_global_native_sealed_inputs
set_option pp.all true in
#check @fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector
#print axioms fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector
end ShielddSecurity.TransferAbsentStartPublication01
