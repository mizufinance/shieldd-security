import ShielddSecurity.TransferFixedFinalizerPublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferNativeGetterPublication01
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
/-! Successful default native-only walk derives global vector capacity/domain,
so the actual sealed enum is supported. Install the same finite native decoder
used by the walk as the publication getter and derive its exact reached enum
observation from the restricted supported native roundtrip. No caller reached
getter equality/capacity/domain supplied. Actual native codec/Clone/getter/
selectors/full trace/cache/ownership/OS correspondence remains explicit. -/

def installGetterIo {O E A : Type} (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → FinalizationWrites O E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject O) E A) : TransferEndToEnd01.Io (ExtendedObject O) E A :=
  installFixedIo encodeNative decodeNative writesOf
    {baseIo with ending := {baseIo.ending with decodePending := TransferPendingFiniteCodec01.decode (decodeObject decodeNative)}}

theorem native_default_walk_derives_supported_global_sealed_enum {O E K X Tree A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (requests : List (Request (ExtendedObject O) E K X Tree A))
    (parent : State (ExtendedObject O)) (queued : List A) (final : State (ExtendedObject O) × List A)
    (storedNativeDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (.inl (encodeNative (.opened [] []))))
    (nativeInputs : ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus)
    (walkedNative : TransferBlockPendingSequence01.walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final) :
    nativeSupported (.sealed (allInputs requests)) = true := by
  have emptyBounded : BoundedPending TransferCurrentPendingReplay01.emptyPending := by
    intro key inside
    cases inside
  have storedDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (TransferPendingFiniteCodec01.encode (encodeObject encodeNative) TransferCurrentPendingReplay01.emptyPending) := by
    rw [TransferBoundedNativeCodec01.supported_pending_encoding_is_actual_native_branch encodeNative
      TransferCurrentPendingReplay01.emptyPending (Nat.zero_le blockCapacity) emptyBounded]
    exact storedNativeDefault
  have totalRoundtrip0 := TransferBoundedNativeCodec01.restricted_native_roundtrip_totalizes_only_with_separate_unsupported_ghosts encodeNative decodeNative supportedRoundtrip
  have coherentRoundtrip0 := TransferPendingFiniteCodec01.typed_finite_codec_restores_coherent_pending
    (encodeObject encodeNative) (decodeObject decodeNative) totalRoundtrip0
  have emptyRead0 : parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent = TransferCurrentPendingReplay01.emptyPending :=
    TransferReachablePendingBlock01.coherent_encoded_current_derives
      (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
      coherentRoundtrip0 _ ⟨parent, (empty : Cache (ExtendedObject O) Unit)⟩ TransferCurrentPendingReplay01.emptyPending
      (TransferPendingSetInvariant01.empty_pending_invariant blockCapacity).1 (by simpa only [apply_empty] using storedDefault)
  have initial0 : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent) := by
    rw [emptyRead0]
    exact TransferPendingSetInvariant01.empty_pending_invariant blockCapacity
  have bounded0 : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent) := by
    rw [emptyRead0]
    exact emptyBounded
  have erasedWalk := TransferNativeReachableErasure01.bounded_reachable_block_walk_erases_unsupported_encoder_ghosts
    encodeNative decodeNative supportedRoundtrip project injection requests parent queued initial0 bounded0 nativeInputs
  have walked : TransferBlockPendingSequence01.walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final := erasedWalk.trans walkedNative
  have order := TransferReachablePendingBlock01.empty_start_reachable_walk_derives_global_inputs
    (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
    coherentRoundtrip0 project injection requests parent queued final emptyRead0 walked
  have bounds := TransferBoundedNativeCodec01.bounded_whole_input_vector_from_native_action_projections requests nativeInputs
  simp only [nativeSupported, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨order.2.2.2.1, bounds⟩

theorem native_getter_source_finalization_publishes_exact_global_mathematical_input_vector {O E K X Tree A I : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject O) E K X Tree A I inputs))
    (parent : State (ExtendedObject O)) (queued : List A) (final : State (ExtendedObject O) × List A)
    (storedNativeDefault : parent.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) =
      some (.inl (encodeNative (.opened [] []))))
    (walkedNative : TransferBlockPendingSequence01.walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode parent queued (installRequests inputs wordOf sourceRequests) = some final)
    (writesOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → FinalizationWrites O E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject O) E A) (host : TransferHostSealedCommit01.Host (ExtendedObject O))
    (height : Fin (2 ^ 64)) (root : Nat) (currentState : host.active = final.1)
    (success : (TransferEndToEnd01.execute (installGetterIo encodeNative decodeNative writesOf baseIo) host height final.2).root = some root) :
    allInputs (installRequests inputs wordOf sourceRequests) = (sourceRequests.flatMap (fun request => typedWords inputs wordOf request.base.action)).map montgomeryValue ∧
    ∃ state,
      (TransferHostEndBlock01.transferred (installGetterIo encodeNative decodeNative writesOf baseIo).ending host height final.2).returned = some state ∧
      state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) = some (.inl (encodeNative (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) ∧
      (allInputs (installRequests inputs wordOf sourceRequests)).Nodup ∧ (allInputs (installRequests inputs wordOf sourceRequests)).length ≤ blockCapacity ∧
      (∀ key ∈ allInputs (installRequests inputs wordOf sourceRequests), key < nullifierModulus) ∧
      ∃ (frozen : TransferWriterPrepareSource01.Frozen), frozen.insertions.accepted = allInputs (installRequests inputs wordOf sourceRequests) ∧ frozen.next.applicationRoot = some root ∧
        (TransferEndToEnd01.execute (installGetterIo encodeNative decodeNative writesOf baseIo) host height final.2).host.writer = .ready frozen.next ∧
        (TransferEndToEnd01.execute (installGetterIo encodeNative decodeNative writesOf baseIo) host height final.2).host.phase = .idle ∧
        (TransferEndToEnd01.execute (installGetterIo encodeNative decodeNative writesOf baseIo) host height final.2).host.store.actualRoots = frozen.next.nullifiers.roots ∧
        (TransferEndToEnd01.execute (installGetterIo encodeNative decodeNative writesOf baseIo) host height final.2).host.store.boundary = some frozen.next.nullifiers := by
  let requests := installRequests inputs wordOf sourceRequests
  have sourceProjection := TransferInstalledSourcePublication01.installed_request_batch_derives_every_source_projection inputs wordOf sourceRequests
  have nativeInputs := TransferTypedScalarPublication01.typed_action_projection_derives_canonical_native_input_bounds
    requests (fun request => typedWords inputs wordOf request.action) sourceProjection
  have supported := native_default_walk_derives_supported_global_sealed_enum encodeNative decodeNative supportedRoundtrip
    keyCode TransferInjectiveKeyPublication01.keyCode_is_injective requests parent queued final storedNativeDefault nativeInputs walkedNative
  let getterBase : TransferEndToEnd01.Io (ExtendedObject O) E A :=
    {baseIo with ending := {baseIo.ending with decodePending := TransferPendingFiniteCodec01.decode (decodeObject decodeNative)}}
  have typedGetter : (installFixedIo encodeNative decodeNative writesOf getterBase).ending.decodePending
      (.inl (encodeNative (.sealed (allInputs requests)))) = restore (.sealed (allInputs requests)) := by
    change restore (decodeNative (encodeNative (.sealed (allInputs requests)))) = restore (.sealed (allInputs requests))
    exact supportedRoundtrip _ supported
  exact TransferFixedFinalizerPublication01.fixed_known_source_finalization_publishes_exact_global_mathematical_input_vector
    encodeNative decodeNative supportedRoundtrip inputs wordOf sourceRequests parent queued final storedNativeDefault
    walkedNative writesOf getterBase host height root currentState typedGetter success
set_option pp.all true in
#check @installGetterIo
#print axioms installGetterIo
set_option pp.all true in
#check @native_default_walk_derives_supported_global_sealed_enum
#print axioms native_default_walk_derives_supported_global_sealed_enum
set_option pp.all true in
#check @native_getter_source_finalization_publishes_exact_global_mathematical_input_vector
#print axioms native_getter_source_finalization_publishes_exact_global_mathematical_input_vector
end ShielddSecurity.TransferNativeGetterPublication01
