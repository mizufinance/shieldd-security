import ShielddSecurity.TransferNativeReachableErasure01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferNativeOnlyPublication01
open TransferStateDelta
open TransferPendingFiniteCodec01 (NativePending restore)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject decodeObject BoundedPending nativeSupported nullifierModulus)
open TransferPendingSetInvariant01 (Invariant)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBlockPendingSequence01 (Request parentPending allInputs)
/-! Actual native-only source default object and block walk join to the exact
global sealed object/accepted vector/application root/physical recovered
boundary of the ordinary source publication pipeline. The ghost-extended
encoder walk is derived equal, not supplied. Ending getter correspondence is
only at the single actual canonical sealed enum; no universal ghost-state or
all-supported-native getter premise. Actual reached finalization field,
supported native roundtrip, canonical input projection, exact current state,
source callbacks/typed keys/Clone/snapshot/ownership/OS remain interfaces.
Same extended object type persists; this is model composition, not native
Rust trace or full certification. -/
theorem whole_native_only_default_block_publishes_exact_global_native_sealed_inputs {O E K X Tree A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (requests : List (Request (ExtendedObject O) E K X Tree A))
    (parent : State (ExtendedObject O)) (queued : List A) (final : State (ExtendedObject O) × List A)
    (storedNativeDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (.inl (encodeNative (.opened [] []))))
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
  have nativeFinal := TransferBoundedNativeCodec01.successful_bounded_default_walk_derives_supported_native_final_object
    encodeNative decodeNative supportedRoundtrip project injection requests parent queued final storedDefault nativeInputs walked
  have totalRoundtrip := TransferBoundedNativeCodec01.restricted_native_roundtrip_totalizes_only_with_separate_unsupported_ghosts encodeNative decodeNative supportedRoundtrip
  have coherentRoundtrip := TransferPendingFiniteCodec01.typed_finite_codec_restores_coherent_pending
    (encodeObject encodeNative) (decodeObject decodeNative) totalRoundtrip
  have emptyRead : parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent = TransferCurrentPendingReplay01.emptyPending :=
    TransferReachablePendingBlock01.coherent_encoded_current_derives
      (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
      coherentRoundtrip _ ⟨parent, (empty : Cache (ExtendedObject O) Unit)⟩ TransferCurrentPendingReplay01.emptyPending
      (TransferPendingSetInvariant01.empty_pending_invariant blockCapacity).1 (by simpa only [apply_empty] using storedDefault)
  have order := TransferReachablePendingBlock01.empty_start_reachable_walk_derives_global_inputs
    (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
    coherentRoundtrip project injection requests parent queued final emptyRead walked
  obtain ⟨_, _, _, _, state, frozen, _, _, taken, accepted, _, _, appRoot, _, _, _, _, idle, _, ready, _, _, roots, stored, _⟩ :=
    TransferEndToEnd01.whole_returned_pipeline_derives_exact_inputs_same_boundary_and_actual_physical_recovery io host height final.2 root success
  have initial : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.ending.project host.active) := by
    rw [projectedKeys, currentState]; exact nativeFinal.1
  have bounded : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.ending.project host.active) := by
    rw [projectedKeys, currentState]; exact nativeFinal.2.1
  have actualObject := TransferNativeSealTransfer01.actual_finalization_transfer_preserves_supported_native_sealed_pending_object
    encodeNative decodeNative io.ending host height final.2 initial bounded finalization state taken
  rw [projectedKeys, currentState, order.2.1] at actualObject
  have keyBounds := TransferBoundedNativeCodec01.bounded_whole_input_vector_from_native_action_projections requests nativeInputs
  have exactTakenInputs : (parentPending io.ending.decodePending io.ending.project state).ordered = allInputs requests := by
    simp only [parentPending, TransferCurrentPendingReplay01.currentPending, apply_empty, projectedKeys, actualObject,
      typedGetter, restore]
  have exactAccepted : frozen.insertions.accepted = allInputs requests := accepted.trans exactTakenInputs
  exact ⟨state, taken, actualObject, order.2.2.1, order.2.2.2.1, keyBounds, frozen, exactAccepted, appRoot, ready, idle, roots, stored⟩

set_option pp.all true in
#check @whole_native_only_default_block_publishes_exact_global_native_sealed_inputs
#print axioms whole_native_only_default_block_publishes_exact_global_native_sealed_inputs
end ShielddSecurity.TransferNativeOnlyPublication01
