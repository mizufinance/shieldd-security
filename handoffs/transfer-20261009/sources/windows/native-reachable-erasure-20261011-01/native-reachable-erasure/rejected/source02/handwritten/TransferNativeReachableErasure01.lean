import ShielddSecurity.TransferNativeDeliveryErasure01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferNativeReachableErasure01
open TransferStateDelta
open TransferPendingFiniteCodec01 (NativePending erase restore)
open TransferPendingSetInvariant01 (Invariant)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject decodeObject BoundedPending nativeSupported nullifierModulus)
open TransferNullifierConsensusLimits01 (blockCapacity nativeWordMax)
open TransferBlockPendingSequence01 (Request parentPending step walk)

/-! Exact observational erasure across the actual source request step and
symbolic block walk. Bound each new pending value from successful full step
and canonical actual input projections. Every refused step stops the walk;
the native-only and ghost-extended versions return the same Option, exact
parent and queue. No desired per-step invariant or success trace is supplied.
Native-only comparison retains the same extended object type and callbacks;
this is model equality under supported native roundtrip/input/key contracts,
not actual Rust trace/codec/getter/ownership/OS closure or certification. -/

def nativeOnlyEncode {O : Type} (encodeNative : NativePending → O)
    (pending : TransferNullifierBatchSource01.Pending) : ExtendedObject O := .inl (encodeNative (erase pending))

theorem bounded_actual_request_step_erases_unsupported_encoder_ghosts {O E K X Tree A : Type}
    (encodeNative : NativePending → O) (decode : ExtendedObject O → TransferNullifierBatchSource01.Pending)
    (project : Bytes → Nat) (request : Request (ExtendedObject O) E K X Tree A)
    (parent : State (ExtendedObject O)) (queued : List A)
    (initial : Invariant blockCapacity (parentPending decode project parent))
    (bounded : BoundedPending (parentPending decode project parent))
    (nativeInputs : ∀ key ∈ request.config.inputs request.action, key < nullifierModulus) :
    step (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) decode project request parent queued =
      step (nativeOnlyEncode encodeNative) decode project request parent queued := by
  let currentRaw := TransferCurrentPendingReplay01.withPending request.config.raw decode (project TransferNullifierObjectKeys01.nullifierBytes)
  let raw := TransferWholeDurableReadback01.installReader currentRaw request.config.decode request.config.readerKey
    request.config.readBoundary request.config.lockAvailable request.config.hash request.config.verify request.config.candidate
  have initialChild : Invariant blockCapacity (raw.nullifiers.pending ⟨parent, (empty : Cache (ExtendedObject O) E)⟩) := by
    change Invariant blockCapacity (TransferCurrentPendingReplay01.currentPending decode
      (project TransferNullifierObjectKeys01.nullifierBytes) ⟨parent, (empty : Cache (ExtendedObject O) E)⟩)
    simpa only [parentPending, TransferCurrentPendingReplay01.currentPending, apply_empty] using initial
  have boundedChild : BoundedPending (raw.nullifiers.pending ⟨parent, (empty : Cache (ExtendedObject O) E)⟩) := by
    change BoundedPending (TransferCurrentPendingReplay01.currentPending decode
      (project TransferNullifierObjectKeys01.nullifierBytes) ⟨parent, (empty : Cache (ExtendedObject O) E)⟩)
    simpa only [parentPending, TransferCurrentPendingReplay01.currentPending, apply_empty] using bounded
  have bodies := TransferNativeDeliveryErasure01.bounded_complete_item_body_ghost_erasure_preserves_every_returned_outcome
    encodeNative raw request.config.notes request.config.volume request.config.sct request.config.volumeAvailable
    request.config.extract request.config.inputs request.config.outputs (nativeWordMax request.config.width)
    (project TransferNullifierObjectKeys01.treeBytes) (project TransferNullifierObjectKeys01.notesBytes)
    (project TransferNullifierObjectKeys01.volumeBytes) request.config.payload (project TransferNullifierObjectKeys01.nullifierBytes)
    request.config.entryKey request.config.dayKey request.context request.action request.item ⟨parent, (empty : Cache (ExtendedObject O) E)⟩
    initialChild boundedChild nativeInputs (TransferNullifierConsensusLimits01.capacity_below_supported_word request.config.width request.supported)
  exact TransferNativeDeliveryErasure01.pointwise_body_equality_derives_exact_delivery_all_index_modes
    request.config.api request.config.keys TransferIndexCountCodec01.codec
    (TransferOrdinaryIndexReadSource01.installReads request.config.convert request.config.indexAvailable)
    (TransferDeferredBodyFailure01.executeBound (TransferNativeRawPending01.nativeRaw encodeNative raw)
      request.config.notes request.config.volume request.config.sct request.config.volumeAvailable request.config.extract request.config.inputs request.config.outputs
      (nativeWordMax request.config.width) blockCapacity (project TransferNullifierObjectKeys01.treeBytes) (project TransferNullifierObjectKeys01.notesBytes)
      (project TransferNullifierObjectKeys01.volumeBytes) request.config.payload (project TransferNullifierObjectKeys01.nullifierBytes) request.config.entryKey request.config.dayKey
      request.context request.action request.item)
    (TransferDeferredBodyFailure01.executeBound (TransferNativeGhostErasure01.nativeOnlyRaw encodeNative raw)
      request.config.notes request.config.volume request.config.sct request.config.volumeAvailable request.config.extract request.config.inputs request.config.outputs
      (nativeWordMax request.config.width) blockCapacity (project TransferNullifierObjectKeys01.treeBytes) (project TransferNullifierObjectKeys01.notesBytes)
      (project TransferNullifierObjectKeys01.volumeBytes) request.config.payload (project TransferNullifierObjectKeys01.nullifierBytes) request.config.entryKey request.config.dayKey
      request.context request.action request.item)
    request.registryMatches request.exclusive request.mode request.action parent queued bodies

theorem bounded_reachable_block_walk_erases_unsupported_encoder_ghosts {O E K X Tree A : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (requests : List (Request (ExtendedObject O) E K X Tree A))
    (parent : State (ExtendedObject O)) (queued : List A)
    (initial : Invariant blockCapacity (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent))
    (bounded : BoundedPending (parentPending (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent))
    (nativeInputs : ∀ request ∈ requests, ∀ key ∈ request.config.inputs request.action, key < nullifierModulus) :
    walk (TransferPendingFiniteCodec01.encode (encodeObject encodeNative)) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests =
      walk (nativeOnlyEncode encodeNative) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project parent queued requests := by
  induction requests generalizing parent queued with
  | nil => rfl
  | cons request rest ih =>
    have actualInputs := nativeInputs request List.mem_cons_self
    have sameStep := bounded_actual_request_step_erases_unsupported_encoder_ghosts encodeNative
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project request parent queued initial bounded actualInputs
    simp only [walk, sameStep]
    cases executed : step (nativeOnlyEncode encodeNative) (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) project request parent queued with
    | none => rfl
    | some committed =>
      have actualSuccess := sameStep.trans executed
      have derived := TransferBoundedNativeCodec01.successful_bounded_whole_step_stores_supported_native_pending
        encodeNative decodeNative supportedRoundtrip project injection request parent queued committed initial bounded actualInputs actualSuccess
      simp only [Option.bind_some]
      exact ih committed.parent committed.deferred derived.1 derived.2.1
        (fun next inside => nativeInputs next (List.mem_cons_of_mem request inside))

set_option pp.all true in
#check @nativeOnlyEncode
#print axioms nativeOnlyEncode
set_option pp.all true in
#check @bounded_actual_request_step_erases_unsupported_encoder_ghosts
#print axioms bounded_actual_request_step_erases_unsupported_encoder_ghosts
set_option pp.all true in
#check @bounded_reachable_block_walk_erases_unsupported_encoder_ghosts
#print axioms bounded_reachable_block_walk_erases_unsupported_encoder_ghosts
end ShielddSecurity.TransferNativeReachableErasure01
