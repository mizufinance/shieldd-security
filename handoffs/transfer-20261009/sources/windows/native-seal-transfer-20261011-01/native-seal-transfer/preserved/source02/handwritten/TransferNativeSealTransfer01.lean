import ShielddSecurity.TransferBoundedNativeCodec01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferNativeSealTransfer01
open TransferStateDelta
open TransferPendingFiniteCodec01 (NativePending restore erase)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject decodeObject nativeSupported BoundedPending nullifierModulus)
open TransferPendingSetInvariant01 (Invariant)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBlockPendingSequence01 (Request parentPending allInputs)

/-! Cover the next pending-object write, SCT seal, and actual post-finalization
state transfer. Supported canonical Fq input domain is inherited exactly.
The modeled source seal stores the native Sealed enum representation of its current
bounded ordered vector; successful concrete transfer preserves that actual
object. The native finalization field correspondence at the actual reached state remains explicit and
does not supply a desired vector or commit callback. The whole default-block
join combines this actual transferred native object with the same exact global
input order, capacity and canonical value bounds. Other-object embedding,
typed/Clone/Any/Arc, component panics, native traces/ownership/locks/snapshot
coherence/ICS23/partition/OS contracts and genuine replay remain interfaces. -/

theorem bounded_source_sct_seal_writes_supported_native_sealed_enum {O : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending) (project : Bytes → Nat)
    (state : State (ExtendedObject O))
    (initial : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state))
    (bounded : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state)) :
    (TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state).objects
        (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (.inl (encodeNative (.sealed (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state).ordered))) := by
  have opened : (TransferCurrentPendingReplay01.currentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
      (project TransferNullifierObjectKeys01.nullifierBytes) ⟨state, (empty : Cache (ExtendedObject O) Unit)⟩).sealed = false := initial.2.2.2
  have stored := (TransferPendingSealSource01.opened_seal_derives_single_object_and_frames
    (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative))
    (project TransferNullifierObjectKeys01.nullifierBytes) ⟨state, (empty : Cache (ExtendedObject O) Unit)⟩ opened).2.2.2.2.2
  have frozenBounded : BoundedPending (TransferPendingSealSource01.freeze (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state)) := bounded
  have encoded := TransferBoundedNativeCodec01.supported_pending_encoding_is_actual_native_branch encodeNative
    (TransferPendingSealSource01.freeze (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state))
    initial.2.2.1 frozenBounded
  change (TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
    (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project state).objects _ = _ at stored
  rw [stored, encoded]
  rfl

theorem actual_finalization_transfer_preserves_supported_native_sealed_pending_object {O E A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (io : TransferHostEndBlock01.Io (ExtendedObject O) E A)
    (host : TransferHostSealedCommit01.Host (ExtendedObject O)) (height : Fin (2 ^ 64)) (queued : List A)
    (initial : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.project host.active))
    (bounded : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.project host.active))
    (finalization : (TransferHostEndBlock01.finalized io host height queued).state.objects (io.project TransferNullifierObjectKeys01.nullifierBytes) =
      (TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
        (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.project host.active).objects (io.project TransferNullifierObjectKeys01.nullifierBytes))
    (returned : State (ExtendedObject O))
    (taken : (TransferHostEndBlock01.transferred io host height queued).returned = some returned) :
    returned.objects (io.project TransferNullifierObjectKeys01.nullifierBytes) =
      some (.inl (encodeNative (.sealed (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.project host.active).ordered))) := by
  have takeFrames := TransferGlobalCommitJoin01.successful_actual_state_transfer_frames_original_pending_objects
    io.transfer io.decodePending (io.project TransferNullifierObjectKeys01.nullifierBytes) io.keys io.convert io.available
    io.deferred io.exclusive (io.flushHeight (TransferHostEndBlock01.finalized io host height queued).state)
    (TransferHostEndBlock01.finalized io host height queued).state returned (TransferHostEndBlock01.finalized io host height queued).queued taken
  rw [takeFrames.1, finalization]
  exact bounded_source_sct_seal_writes_supported_native_sealed_enum encodeNative decodeNative io.project host.active initial bounded

theorem whole_bounded_publication_transfers_native_sealed_exact_global_input_vector {O E K X Tree A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (requests : List (Request (ExtendedObject O) E K X Tree A))
    (parent : State (ExtendedObject O)) (queued : List A) (final : State (ExtendedObject O) × List A)
    (storedDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (TransferPendingFiniteCodec01.encode (encodeObject encodeNative) TransferCurrentPendingReplay01.emptyPending))
    (nativeInputs : ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus)
    (walked : TransferBlockPendingSequence01.walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests = some final)
    (io : TransferEndToEnd01.Io (ExtendedObject O) E A) (host : TransferHostSealedCommit01.Host (ExtendedObject O))
    (height : Fin (2 ^ 64)) (root : Nat) (currentState : host.active = final.1)
    (projectedKeys : io.ending.project = project)
    (typedGetter : ∀ native, nativeSupported native = true → io.ending.decodePending (.inl (encodeNative native)) = restore native)
    (finalization : (TransferHostEndBlock01.finalized io.ending host height final.2).state.objects (io.ending.project TransferNullifierObjectKeys01.nullifierBytes) =
      (TransferGlobalCommitJoin01.sealedState (TransferPendingFiniteCodec01.encode (encodeObject encodeNative))
        (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) io.ending.project host.active).objects (io.ending.project TransferNullifierObjectKeys01.nullifierBytes))
    (success : (TransferEndToEnd01.execute io host height final.2).root = some root) :
    ∃ state,
      (TransferHostEndBlock01.transferred io.ending host height final.2).returned = some state ∧
      state.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (.inl (encodeNative (.sealed (allInputs requests)))) ∧
      (allInputs requests).Nodup ∧ (allInputs requests).length ≤ blockCapacity ∧
      (∀ key ∈ allInputs requests, key < nullifierModulus) ∧
      ∃ frozen, frozen.insertions.accepted = allInputs requests ∧ frozen.next.applicationRoot = some root ∧
        (TransferEndToEnd01.execute io host height final.2).host.writer = .ready frozen.next ∧
        (TransferEndToEnd01.execute io host height final.2).host.phase = .idle ∧
        (TransferEndToEnd01.execute io host height final.2).host.store.actualRoots = frozen.next.nullifiers.roots ∧
        (TransferEndToEnd01.execute io host height final.2).host.store.boundary = some frozen.next.nullifiers := by
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
  have actualObject := actual_finalization_transfer_preserves_supported_native_sealed_pending_object
    encodeNative decodeNative io.ending host height final.2 initial bounded finalization state taken
  rw [projectedKeys, currentState, order.2.1] at actualObject
  have keyBounds := TransferBoundedNativeCodec01.bounded_whole_input_vector_from_native_action_projections requests nativeInputs
  have supported : nativeSupported (.sealed (allInputs requests)) = true := by
    simp only [TransferBoundedNativeCodec01.nativeSupported, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨order.2.2.2.1, keyBounds⟩
  have exactTakenInputs : (parentPending io.ending.decodePending io.ending.project state).ordered = allInputs requests := by
    simp only [parentPending, TransferCurrentPendingReplay01.currentPending, apply_empty, projectedKeys, actualObject,
      typedGetter (.sealed (allInputs requests)) supported, restore]
  have exactAccepted : frozen.insertions.accepted = allInputs requests := accepted.trans exactTakenInputs
  exact ⟨state, taken, actualObject, order.2.2.1, order.2.2.2.1, keyBounds, frozen, exactAccepted, appRoot, ready, idle, roots, stored⟩

set_option pp.all true in
#check @bounded_source_sct_seal_writes_supported_native_sealed_enum
#print axioms bounded_source_sct_seal_writes_supported_native_sealed_enum
set_option pp.all true in
#check @actual_finalization_transfer_preserves_supported_native_sealed_pending_object
#print axioms actual_finalization_transfer_preserves_supported_native_sealed_pending_object
set_option pp.all true in
#check @whole_bounded_publication_transfers_native_sealed_exact_global_input_vector
#print axioms whole_bounded_publication_transfers_native_sealed_exact_global_input_vector
end ShielddSecurity.TransferNativeSealTransfer01
