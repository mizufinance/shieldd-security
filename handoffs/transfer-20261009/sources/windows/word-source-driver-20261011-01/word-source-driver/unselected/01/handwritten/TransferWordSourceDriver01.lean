import ShielddSecurity.TransferWordObjectCodec01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWordSourceDriver01
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
open TransferTaggedCodecPublication01 (OtherFinalizationWrites)
open TransferWordObjectCodec01 (WordTaggedObject encodeNative decodeNative liftWordWrites)
open TransferBlockPendingSequence01 (step walk)
open TransferAbsentStartPublication01 (freshParent)
/-! Whole returned source driver constructs the successful request walk and executes its reached state with source-ordered known finalization. Typed word-field pending/object codec is instantiated directly: actual successful empty-start walk derives canonical bounded global inputs, yielding concrete getter correspondence without supplied codec/getter/domain/final-object premises. Exact ordered typed mathematical source vector, supported sealed word object, frozen accepted insertions, same application root, Ready/Idle physical roots and committed boundary follow from returned root success. Five audited declarations: two definitions and three theorems. Native imbl/private Scalar/Any/downcast/Clone/primitive/compiler/Choice/CtOption/full callee/value/trace/ownership/OS bindings and older extended ghost carrier remain explicit. No ancestor replay; zero native/control/certification credit; full Transfer OPEN. -/

def installSourceOrderedTaggedIo {Other E A : Type}
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (WordTaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (WordTaggedObject Other)) E A) :
    TransferEndToEnd01.Io (ExtendedObject (WordTaggedObject Other)) E A :=
  TransferSourceOrderedFinalizer01.installFixedIo encodeNative decodeNative
    (fun height state queued => liftWordWrites (writesOf height state queued))
    {baseIo with ending := {baseIo.ending with decodePending := TransferPendingFiniteCodec01.decode (decodeObject decodeNative)}}


theorem successful_fresh_word_walk_derives_exact_sealed_codec_domain {Other E K X Tree A : Type}
    (requests : List (Request (ExtendedObject (WordTaggedObject Other)) E K X Tree A))
    (parent : State (ExtendedObject (WordTaggedObject Other))) (queued : List A)
    (final : State (ExtendedObject (WordTaggedObject Other)) × List A)
    (absent : parent.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) = none)
    (nativeInputs : ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus)
    (walkedNative : walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode parent queued requests = some final) :
    (allInputs requests).Nodup ∧ (allInputs requests).length ≤ blockCapacity ∧
      (∀ key ∈ allInputs requests, key < nullifierModulus) := by
  have supportedRoundtrip := TransferWordObjectCodec01.supported_word_object_codec_restores_exact_pending_observations (Other := Other)
  have totalRoundtrip := TransferBoundedNativeCodec01.restricted_native_roundtrip_totalizes_only_with_separate_unsupported_ghosts
    (encodeNative (Other := Other)) decodeNative supportedRoundtrip
  have coherentRoundtrip := TransferPendingFiniteCodec01.typed_finite_codec_restores_coherent_pending
    (encodeObject encodeNative) (decodeObject decodeNative) totalRoundtrip
  have emptyRead : parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode parent = TransferCurrentPendingReplay01.emptyPending :=
    TransferCurrentPendingReplay01.current_object_absence_derives_default
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) (keyCode TransferNullifierObjectKeys01.nullifierBytes)
      ⟨parent, (empty : Cache (ExtendedObject (WordTaggedObject Other)) Unit)⟩ (by simpa only [apply_empty] using absent)
  have initial : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode parent) := by
    rw [emptyRead]
    exact TransferPendingSetInvariant01.empty_pending_invariant blockCapacity
  have bounded : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode parent) := by
    rw [emptyRead]
    intro key inside
    cases inside
  have erasedWalk := TransferNativeReachableErasure01.bounded_reachable_block_walk_erases_unsupported_encoder_ghosts
    encodeNative decodeNative supportedRoundtrip keyCode TransferInjectiveKeyPublication01.keyCode_is_injective
    requests parent queued initial bounded nativeInputs
  have walked : walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode parent queued requests = some final := erasedWalk.trans walkedNative
  have order := TransferReachablePendingBlock01.empty_start_reachable_walk_derives_global_inputs
    (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
    coherentRoundtrip keyCode TransferInjectiveKeyPublication01.keyCode_is_injective requests parent queued final emptyRead walked
  exact ⟨order.2.2.1, order.2.2.2.1,
    TransferBoundedNativeCodec01.bounded_whole_input_vector_from_native_action_projections requests nativeInputs⟩

theorem fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector {Other E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject (WordTaggedObject Other)) E K X Tree A I inputs))
    (verifiable nonverifiable : View Bytes) (otherObjects : View (ExtendedObject (WordTaggedObject Other))) (queued : List A) (final : State (ExtendedObject (WordTaggedObject Other)) × List A)
    (walkedNative : TransferBlockPendingSequence01.walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode (freshParent verifiable nonverifiable otherObjects) queued (installRequests inputs wordOf sourceRequests) = some final)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (WordTaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (WordTaggedObject Other)) E A) (host : TransferHostSealedCommit01.Host (ExtendedObject (WordTaggedObject Other)))
    (height : Fin (2 ^ 64)) (root : Nat) (currentState : host.active = final.1)
    (success : (TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) host height final.2).root = some root) :
    allInputs (installRequests inputs wordOf sourceRequests) = (sourceRequests.flatMap (fun request => typedWords inputs wordOf request.base.action)).map montgomeryValue ∧
    ∃ state,
      (TransferHostEndBlock01.transferred (installSourceOrderedTaggedIo writesOf baseIo).ending host height final.2).returned = some state ∧
      state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) = some (.inl (encodeNative (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) ∧
      (allInputs (installRequests inputs wordOf sourceRequests)).Nodup ∧ (allInputs (installRequests inputs wordOf sourceRequests)).length ≤ blockCapacity ∧
      (∀ key ∈ allInputs (installRequests inputs wordOf sourceRequests), key < nullifierModulus) ∧
      ∃ (frozen : TransferWriterPrepareSource01.Frozen), frozen.insertions.accepted = allInputs (installRequests inputs wordOf sourceRequests) ∧ frozen.next.applicationRoot = some root ∧
        (TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) host height final.2).host.writer = .ready frozen.next ∧
        (TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) host height final.2).host.phase = .idle ∧
        (TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) host height final.2).host.store.actualRoots = frozen.next.nullifiers.roots ∧
        (TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) host height final.2).host.store.boundary = some frozen.next.nullifiers := by
  let requests := installRequests inputs wordOf sourceRequests
  let parent := freshParent verifiable nonverifiable otherObjects
  let io := installSourceOrderedTaggedIo writesOf baseIo
  have sourceProjection := TransferInstalledSourcePublication01.installed_request_batch_derives_every_source_projection inputs wordOf sourceRequests
  have nativeInputs := TransferTypedScalarPublication01.typed_action_projection_derives_canonical_native_input_bounds
    requests (fun request => typedWords inputs wordOf request.action) sourceProjection
  have absent : parent.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) = none := by
    simp only [parent, freshParent, ite_true]
  have domain := successful_fresh_word_walk_derives_exact_sealed_codec_domain requests parent queued final absent nativeInputs walkedNative
  have getter : io.ending.decodePending (.inl (encodeNative (.sealed (allInputs requests)))) = restore (.sealed (allInputs requests)) :=
    TransferWordObjectCodec01.canonical_bounded_sealed_word_object_getter_recovers_exact_ordered_pending (Other := Other)
      (allInputs requests) domain.2.1 domain.2.2
  have frame := TransferKnownFinalizerPublication01.installed_known_finalizer_derives_reached_publication_field_frame
    (encodeNative (Other := Other)) (decodeNative (Other := Other)) keyCode TransferInjectiveKeyPublication01.keyCode_is_injective
    (fun height state queued => TransferSourceOrderedFinalizer01.toEffects (liftWordWrites (writesOf height state queued)))
    {baseIo with ending := {baseIo.ending with decodePending := TransferPendingFiniteCodec01.decode (decodeObject decodeNative)}}
    host height final.2
  have values := TransferTypedScalarPublication01.global_source_input_vector_is_exact_typed_montgomery_projection
    requests (fun request => typedWords inputs wordOf request.action) sourceProjection
  refine ⟨values.trans ?_, ?_⟩
  · exact congrArg (fun words : List (Vector UInt64 4) => words.map montgomeryValue)
      (TransferInstalledSourcePublication01.installed_request_batch_retains_exact_ordered_source_word_vector inputs wordOf sourceRequests)
  · exact TransferAbsentStartPublication01.whole_absent_native_default_block_publishes_exact_global_native_sealed_inputs
      (encodeNative (Other := Other)) (decodeNative (Other := Other))
      (fun native supported => TransferWordObjectCodec01.supported_word_object_codec_restores_exact_pending_observations native supported)
      keyCode TransferInjectiveKeyPublication01.keyCode_is_injective requests parent queued final absent nativeInputs walkedNative
      io host height root currentState rfl getter frame success
def runCompleteBlock {Other E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject (WordTaggedObject Other)) E K X Tree A I inputs))
    (verifiable nonverifiable : View Bytes) (otherObjects : View (ExtendedObject (WordTaggedObject Other))) (queued : List A)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (WordTaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (WordTaggedObject Other)) E A)
    (host : TransferHostSealedCommit01.Host (ExtendedObject (WordTaggedObject Other))) (height : Fin (2 ^ 64)) :
    Option (TransferEndToEnd01.Outcome (ExtendedObject (WordTaggedObject Other)) A) :=
  (walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
    (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode
    (freshParent verifiable nonverifiable otherObjects) queued (installRequests inputs wordOf sourceRequests)).map
    (fun final => TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) {host with active := final.1} height final.2)

theorem returned_whole_block_derives_actual_walk_exact_inputs_and_publication {Other E K X Tree A I : Type}
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject (WordTaggedObject Other)) E K X Tree A I inputs))
    (verifiable nonverifiable : View Bytes) (otherObjects : View (ExtendedObject (WordTaggedObject Other))) (queued : List A)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject (WordTaggedObject Other)) → List A → OtherFinalizationWrites Other E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject (WordTaggedObject Other)) E A)
    (host : TransferHostSealedCommit01.Host (ExtendedObject (WordTaggedObject Other))) (height : Fin (2 ^ 64))
    (outcome : TransferEndToEnd01.Outcome (ExtendedObject (WordTaggedObject Other)) A) (root : Nat)
    (returned : runCompleteBlock inputs wordOf sourceRequests verifiable nonverifiable otherObjects queued writesOf baseIo host height = some outcome)
    (success : outcome.root = some root) :
    ∃ final : State (ExtendedObject (WordTaggedObject Other)) × List A,
      walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
        (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode
        (freshParent verifiable nonverifiable otherObjects) queued (installRequests inputs wordOf sourceRequests) = some final ∧
      outcome = TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) {host with active := final.1} height final.2 ∧
      allInputs (installRequests inputs wordOf sourceRequests) =
        (sourceRequests.flatMap (fun request => typedWords inputs wordOf request.base.action)).map montgomeryValue ∧
      ∃ state,
        (TransferHostEndBlock01.transferred (installSourceOrderedTaggedIo writesOf baseIo).ending {host with active := final.1} height final.2).returned = some state ∧
        state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) =
          some (.inl (encodeNative (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) ∧
        (allInputs (installRequests inputs wordOf sourceRequests)).Nodup ∧
        (allInputs (installRequests inputs wordOf sourceRequests)).length ≤ blockCapacity ∧
        (∀ key ∈ allInputs (installRequests inputs wordOf sourceRequests), key < nullifierModulus) ∧
        ∃ (frozen : TransferWriterPrepareSource01.Frozen),
          frozen.insertions.accepted = allInputs (installRequests inputs wordOf sourceRequests) ∧ frozen.next.applicationRoot = some root ∧
          outcome.host.writer = .ready frozen.next ∧ outcome.host.phase = .idle ∧
          outcome.host.store.actualRoots = frozen.next.nullifiers.roots ∧ outcome.host.store.boundary = some frozen.next.nullifiers := by
  cases ran : walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode
      (freshParent verifiable nonverifiable otherObjects) queued (installRequests inputs wordOf sourceRequests) with
  | none =>
    simp only [runCompleteBlock, ran, Option.map_none] at returned
    cases returned
  | some final =>
    have same : TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) {host with active := final.1} height final.2 = outcome :=
      Option.some.inj (by simpa only [runCompleteBlock, ran, Option.map_some] using returned)
    have rootSuccess : (TransferEndToEnd01.execute (installSourceOrderedTaggedIo writesOf baseIo) {host with active := final.1} height final.2).root = some root := by
      rw [same]
      exact success
    have publication := fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector
      inputs wordOf sourceRequests verifiable nonverifiable otherObjects queued final ran writesOf baseIo
      {host with active := final.1} height root rfl rootSuccess
    refine ⟨final, rfl, same.symm, ?_⟩
    simpa only [same] using publication

set_option pp.all true in
#check @successful_fresh_word_walk_derives_exact_sealed_codec_domain
#print axioms successful_fresh_word_walk_derives_exact_sealed_codec_domain
set_option pp.all true in
#check @installSourceOrderedTaggedIo
#print axioms installSourceOrderedTaggedIo
set_option pp.all true in
#check @fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector
#print axioms fresh_absent_source_finalization_publishes_exact_global_mathematical_input_vector
set_option pp.all true in
#check @runCompleteBlock
#print axioms runCompleteBlock
set_option pp.all true in
#check @returned_whole_block_derives_actual_walk_exact_inputs_and_publication
#print axioms returned_whole_block_derives_actual_walk_exact_inputs_and_publication
end ShielddSecurity.TransferWordSourceDriver01
