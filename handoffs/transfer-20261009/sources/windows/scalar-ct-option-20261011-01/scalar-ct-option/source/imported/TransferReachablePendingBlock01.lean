import ShielddSecurity.TransferPendingFiniteCodec01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferReachablePendingBlock01
open TransferStateDelta TransferIndexWriterModel01
open TransferNullifierBatchSource01 (Pending)
open TransferPendingSetInvariant01 (Invariant Coherent)
open TransferNullifierConsensusLimits01 (SupportedWidth blockCapacity nativeWordMax)
open TransferBlockPendingSequence01 (Request parentPending bindPending step walk allInputs)
open TransferPendingSealSource01 (sealOnce freeze ensureSealed SealError)

/-! The same source whole step/walk/freeze now uses typed codec roundtrip only
for coherent states. Successful actual inspection derives next coherence before
any roundtrip use; frozen membership is coherent by construction. The finite
enum wrapper uses order-only Sealed storage and reconstructed ghost membership,
so no arbitrary membership-function roundtrip is assumed. Primitive native
typed object embedding/Clone, finite collections, actual nullifier values,
whole program scheduling/owner, reader/crypto/Host/durability remain explicit.
No native or full Transfer certification. Finite symbolic list induction. -/

theorem coherent_encoded_current_derives {O E : Type} (encode : Pending → O) (decode : O → Pending)
    (roundtrip : ∀ pending, Coherent pending → decode (encode pending) = pending)
    (objectKey : Nat) (child : Delta O E) (pending : Pending) (coherent : Coherent pending)
    (stored : (applyCache child.parent child.cache).objects objectKey = some (encode pending)) :
    TransferCurrentPendingReplay01.currentPending decode objectKey child = pending := by
  simp only [TransferCurrentPendingReplay01.currentPending, stored, roundtrip pending coherent]

theorem whole_step_preserves_reachable_pending_codec {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (roundtrip : ∀ pending, Coherent pending → decode (encode pending) = pending)
    (project : Bytes → Nat) (injection : Function.Injective project) (request : Request O E K X Tree A)
    (parent : State O) (queued : List A) (committed : Commit O E A)
    (initial : Invariant blockCapacity (parentPending decode project parent))
    (success : step encode decode project request parent queued = some committed) :
    Invariant blockCapacity (parentPending decode project committed.parent) ∧
      (parentPending decode project committed.parent).ordered = (parentPending decode project parent).ordered ++ request.config.inputs request.action ∧
      committed.parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (encode (parentPending decode project committed.parent)) := by
  let config := request.config
  let raw := TransferWholeDurableReadback01.installReader
    (bindPending config encode decode project).raw config.decode config.readerKey config.readBoundary config.lockAvailable config.hash config.verify config.candidate
  obtain ⟨pending, inspected, stored, ordered, _, _, _⟩ :=
    TransferNullifierObjectKeys01.whole_success_retains_source_key_pending_nullifier_encoding config.api config.keys config.convert config.indexAvailable
      raw config.notes config.volume config.sct config.volumeAvailable config.extract config.inputs config.outputs project injection
      (nativeWordMax config.width) blockCapacity config.payload config.entryKey config.dayKey request.context request.action request.item
      request.registryMatches request.exclusive request.mode parent queued committed request.nonempty
      (TransferNullifierConsensusLimits01.capacity_below_supported_word config.width request.supported) success
  have previous : raw.nullifiers.pending ⟨parent, (empty : Cache O E)⟩ = parentPending decode project parent := by
    change TransferCurrentPendingReplay01.currentPending decode (project TransferNullifierObjectKeys01.nullifierBytes)
      ⟨parent, (empty : Cache O E)⟩ = parentPending decode project parent
    simp only [TransferCurrentPendingReplay01.currentPending, parentPending, apply_empty]
  have coherent : TransferPendingSetInvariant01.Coherent (raw.nullifiers.pending ⟨parent, (empty : Cache O E)⟩) := by
    rw [previous]
    exact initial.1
  have nodup : (raw.nullifiers.pending ⟨parent, (empty : Cache O E)⟩).ordered.Nodup := by
    rw [previous]
    exact initial.2.1
  have invariant := TransferPendingSetInvariant01.successful_inspection_preserves_invariant raw.nullifiers (nativeWordMax config.width)
    blockCapacity ⟨parent, (empty : Cache O E)⟩ (config.inputs request.action) pending coherent nodup
    (TransferNullifierConsensusLimits01.capacity_below_supported_word config.width request.supported) inspected
  have after : parentPending decode project committed.parent = pending := by
    exact coherent_encoded_current_derives encode decode roundtrip _
      ⟨committed.parent, (empty : Cache O Unit)⟩ pending invariant.1 (by simpa only [apply_empty] using stored)
  rw [previous] at ordered
  rw [after]
  exact ⟨invariant, ordered, stored⟩

theorem successful_walk_uses_only_coherent_codec {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (roundtrip : ∀ pending, Coherent pending → decode (encode pending) = pending)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A)
    (initial : Invariant blockCapacity (parentPending decode project parent))
    (success : walk encode decode project parent queued requests = some final) :
    Invariant blockCapacity (parentPending decode project final.1) ∧
      (parentPending decode project final.1).ordered = (parentPending decode project parent).ordered ++ allInputs requests := by
  induction requests generalizing parent queued with
  | nil =>
    have same : (parent, queued) = final := Option.some.inj success
    subst final
    exact ⟨initial, by simp only [allInputs, List.append_nil]⟩
  | cons request rest ih =>
    cases first : step encode decode project request parent queued with
    | none => simp only [walk, first, Option.bind_none] at success; contradiction
    | some committed =>
      have later : walk encode decode project committed.parent committed.deferred rest = some final := by
        simpa only [walk, first, Option.bind_some] using success
      obtain ⟨nextInvariant, nextOrdered, _⟩ := whole_step_preserves_reachable_pending_codec encode decode roundtrip project injection request
        parent queued committed initial first
      obtain ⟨finalInvariant, finalOrdered⟩ := ih committed.parent committed.deferred nextInvariant later
      refine ⟨finalInvariant, ?_⟩
      rw [finalOrdered, nextOrdered]
      exact List.append_assoc _ _ _

theorem empty_start_reachable_walk_derives_global_inputs {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (roundtrip : ∀ pending, Coherent pending → decode (encode pending) = pending)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A)
    (emptyStart : parentPending decode project parent = TransferCurrentPendingReplay01.emptyPending)
    (success : TransferBlockPendingSequence01.walk encode decode project parent queued requests = some final) :
    Invariant blockCapacity (parentPending decode project final.1) ∧
      (parentPending decode project final.1).ordered = allInputs requests ∧ (allInputs requests).Nodup ∧
      (allInputs requests).length ≤ blockCapacity ∧
      ∀ key, (parentPending decode project final.1).membership key = (allInputs requests).contains key := by
  have initial : Invariant blockCapacity (parentPending decode project parent) := by
    rw [emptyStart]
    exact TransferPendingSetInvariant01.empty_pending_invariant blockCapacity
  obtain ⟨invariant, ordered⟩ := successful_walk_uses_only_coherent_codec encode decode roundtrip
    project injection requests parent queued final initial success
  have exactOrder : (parentPending decode project final.1).ordered = allInputs requests := by
    simpa only [emptyStart, TransferCurrentPendingReplay01.emptyPending, List.nil_append] using ordered
  refine ⟨invariant, exactOrder, ?_, ?_, ?_⟩
  · rw [← exactOrder]
    exact invariant.2.1
  · rw [← exactOrder]
    exact invariant.2.2.1
  · intro key
    rw [invariant.1 key, exactOrder]

def BlockSealFacts {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (project : Bytes → Nat)
    (requests : List (Request O E K X Tree A)) (final : State O × List A) : Prop :=
    let output := sealOnce encode decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨final.1, (empty : Cache O Unit)⟩
    let sealedState := applyCache final.1 output.cache
    output.result = .ok () ∧ sealedState.verifiable = final.1.verifiable ∧ sealedState.nonverifiable = final.1.nonverifiable ∧
      output.cache.events = [] ∧ (parentPending decode project sealedState).ordered = allInputs requests ∧
      (allInputs requests).Nodup ∧ (allInputs requests).length ≤ blockCapacity ∧
      (∀ key, (parentPending decode project sealedState).membership key = (allInputs requests).contains key) ∧
      (parentPending decode project sealedState).sealed = true ∧
      ensureSealed decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨sealedState, (empty : Cache O Unit)⟩ = .ok () ∧
      sealOnce encode decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨sealedState, (empty : Cache O Unit)⟩ =
        ⟨(empty : Cache O Unit), .error .alreadySealed⟩ ∧
      ∀ later : Request O E K X Tree A,
        let attempted := TransferBlockPendingSequence01.step encode decode project later sealedState final.2
        attempted = none ∧ finish sealedState final.2 attempted = (sealedState, final.2)

theorem coherent_block_seals_exact_global_inputs_and_refuses_later_staging {O E K X Tree A : Type}
    (encode : Pending → O) (decode : O → Pending) (roundtrip : ∀ pending, Coherent pending → decode (encode pending) = pending)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A)
    (emptyStart : parentPending decode project parent = TransferCurrentPendingReplay01.emptyPending)
    (success : TransferBlockPendingSequence01.walk encode decode project parent queued requests = some final) :
    BlockSealFacts encode decode project requests final := by
  dsimp only [BlockSealFacts]
  have blockFacts := empty_start_reachable_walk_derives_global_inputs encode decode roundtrip
    project injection requests parent queued final emptyStart success
  let child : Delta O Unit := ⟨final.1, empty⟩
  let output := sealOnce encode decode (project TransferNullifierObjectKeys01.nullifierBytes) child
  let sealedState := applyCache final.1 output.cache
  have opened : (TransferCurrentPendingReplay01.currentPending decode (project TransferNullifierObjectKeys01.nullifierBytes) child).sealed = false :=
    blockFacts.1.2.2.2
  have frames := TransferPendingSealSource01.opened_seal_derives_single_object_and_frames encode decode _ child opened
  have stored : sealedState.objects (project TransferNullifierObjectKeys01.nullifierBytes) = some (encode (freeze (parentPending decode project final.1))) :=
    frames.2.2.2.2.2
  have frozenRead : parentPending decode project sealedState = freeze (parentPending decode project final.1) := by
    exact coherent_encoded_current_derives encode decode roundtrip _
      ⟨sealedState, (empty : Cache O Unit)⟩ (freeze (parentPending decode project final.1))
      (TransferPendingSealSource01.freeze_exact_order_membership_and_sealed _).2.1 (by simpa only [apply_empty] using stored)
  have sealed : (parentPending decode project sealedState).sealed = true := by rw [frozenRead]; rfl
  refine ⟨frames.1, ?_, ?_, frames.2.2.2.1, ?_, blockFacts.2.2.1, blockFacts.2.2.2.1, ?_, sealed, ?_, ?_, ?_⟩
  · change overlay final.1.verifiable output.cache.verifiable = final.1.verifiable
    rw [frames.2.1]
    rfl
  · change overlay final.1.nonverifiable output.cache.nonverifiable = final.1.nonverifiable
    rw [frames.2.2.1]
    rfl
  · rw [frozenRead]
    exact blockFacts.2.1
  · intro key
    rw [frozenRead]
    change (parentPending decode project final.1).ordered.contains key = (allInputs requests).contains key
    rw [blockFacts.2.1]
  · change ensureSealed decode (project TransferNullifierObjectKeys01.nullifierBytes) ⟨sealedState, (empty : Cache O Unit)⟩ = .ok ()
    have frozenCoherent := (TransferPendingSealSource01.freeze_exact_order_membership_and_sealed (parentPending decode project final.1)).2.1
    have encodedSealed : (decode (encode (freeze (parentPending decode project final.1)))).sealed = true :=
      congrArg Pending.sealed (roundtrip (freeze (parentPending decode project final.1)) frozenCoherent)
    simp only [ensureSealed, apply_empty, stored, encodedSealed, if_true]
  · exact TransferPendingSealSource01.already_sealed_error_retains_input_cache encode decode _ ⟨sealedState, (empty : Cache O Unit)⟩ sealed
  · intro later
    exact TransferPendingSealSource01.whole_request_after_current_sealing_preserves_parent_and_queue encode decode project injection later sealedState final.2 sealed

theorem finite_codec_default_block_seals_exact_global_inputs {O E K X Tree A : Type}
    (encodeNative : TransferPendingFiniteCodec01.NativePending → O) (decodeNative : O → TransferPendingFiniteCodec01.NativePending)
    (typedRoundtrip : ∀ native, TransferPendingFiniteCodec01.restore (decodeNative (encodeNative native)) = TransferPendingFiniteCodec01.restore native)
    (project : Bytes → Nat) (injection : Function.Injective project) (requests : List (Request O E K X Tree A))
    (parent : State O) (queued : List A) (final : State O × List A)
    (storedDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (TransferPendingFiniteCodec01.encode encodeNative TransferCurrentPendingReplay01.emptyPending))
    (success : walk (TransferPendingFiniteCodec01.encode encodeNative) (TransferPendingFiniteCodec01.decode decodeNative)
      project parent queued requests = some final) :
    BlockSealFacts (TransferPendingFiniteCodec01.encode encodeNative) (TransferPendingFiniteCodec01.decode decodeNative) project requests final := by
  have reachableRoundtrip : ∀ pending, Coherent pending →
      TransferPendingFiniteCodec01.decode decodeNative (TransferPendingFiniteCodec01.encode encodeNative pending) = pending :=
    TransferPendingFiniteCodec01.typed_finite_codec_restores_coherent_pending encodeNative decodeNative typedRoundtrip
  have emptyCoherent : Coherent TransferCurrentPendingReplay01.emptyPending :=
    (TransferPendingSetInvariant01.empty_pending_invariant blockCapacity).1
  have emptyStart : parentPending (TransferPendingFiniteCodec01.decode decodeNative) project parent = TransferCurrentPendingReplay01.emptyPending :=
    coherent_encoded_current_derives (TransferPendingFiniteCodec01.encode encodeNative) (TransferPendingFiniteCodec01.decode decodeNative)
      reachableRoundtrip _ ⟨parent, (empty : Cache O Unit)⟩ TransferCurrentPendingReplay01.emptyPending emptyCoherent
      (by simpa only [apply_empty] using storedDefault)
  exact coherent_block_seals_exact_global_inputs_and_refuses_later_staging (TransferPendingFiniteCodec01.encode encodeNative)
    (TransferPendingFiniteCodec01.decode decodeNative) reachableRoundtrip project injection requests parent queued final emptyStart success

set_option pp.all true in
#check @coherent_encoded_current_derives
#print axioms coherent_encoded_current_derives
set_option pp.all true in
#check @whole_step_preserves_reachable_pending_codec
#print axioms whole_step_preserves_reachable_pending_codec
set_option pp.all true in
#check @successful_walk_uses_only_coherent_codec
#print axioms successful_walk_uses_only_coherent_codec
set_option pp.all true in
#check @empty_start_reachable_walk_derives_global_inputs
#print axioms empty_start_reachable_walk_derives_global_inputs
set_option pp.all true in
#check @BlockSealFacts
#print axioms BlockSealFacts
set_option pp.all true in
#check @coherent_block_seals_exact_global_inputs_and_refuses_later_staging
#print axioms coherent_block_seals_exact_global_inputs_and_refuses_later_staging
set_option pp.all true in
#check @finite_codec_default_block_seals_exact_global_inputs
#print axioms finite_codec_default_block_seals_exact_global_inputs
end ShielddSecurity.TransferReachablePendingBlock01
