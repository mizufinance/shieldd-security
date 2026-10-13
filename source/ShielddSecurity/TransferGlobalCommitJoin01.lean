import ShielddSecurity.TransferEndToEnd01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferGlobalCommitJoin01
open TransferStateDelta
open TransferIndexWriterModel01 (Keys Encoded)
open TransferNullifierBatchSource01 (Pending)
open TransferBlockPendingSequence01 (Request parentPending allInputs)
open TransferHostSealedCommit01 (Host)

/-! Join arbitrary successful whole delivery walks to ordinary Host publication.
Index flush field frames are derived from the concrete source index writer,
without a supplied counter observation or per-step successful poststate.
The only application-finalization field contract here relates its independently
observed returned pending object to the source SCT seal of its actual input.
It does not supply desired prepared/committed vectors, callbacks or roots.
Finite NativePending codec roundtrip and projected source-key injectivity
remain explicit library/representation obligations. Native component panic,
Clone/Any/Arc ownership, immutable snapshots plus separate ICS23 soundness,
temporal physical observations/partition frames/OS durability and runtime
replay remain separate from this conditional source theorem. -/

theorem successful_concrete_flush_frames_pending_objects_without_count_premise {O E A : Type}
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (deferred exclusive : Bool) (height : Option Nat) (parent : State O) (queued : List A)
    (success : (TransferTakeCommitState01.flushFor keys convert available deferred exclusive height parent queued).error = none) :
    (TransferTakeCommitState01.flushFor keys convert available deferred exclusive height parent queued).parent.objects = parent.objects ∧
      (TransferTakeCommitState01.flushFor keys convert available deferred exclusive height parent queued).parent.verifiable = parent.verifiable := by
  unfold TransferTakeCommitState01.flushFor TransferDeferredQueueSourceModel01.flush at success ⊢
  by_cases otherMode : deferred = false
  · simp [otherMode, TransferDeferredQueueSourceModel01.unchanged]
  · simp only [if_neg otherMode] at success ⊢
    by_cases emptyQueue : queued.isEmpty = true
    · simp [emptyQueue, TransferDeferredQueueSourceModel01.unchanged]
    · simp only [if_neg emptyQueue] at success ⊢
      by_cases unavailable : exclusive = false
      · simp only [if_pos unavailable, TransferDeferredQueueSourceModel01.refused] at success; cases success
      · simp only [if_neg unavailable] at success ⊢
        cases height with
        | none => simp only [TransferDeferredQueueSourceModel01.refused] at success; cases success
        | some height =>
          cases walked : TransferDeferredQueueSourceModel01.walk (TransferDeferredCountWalk01.queueWriter keys convert available parent) height empty queued with
          | error error => simp only [walked, TransferDeferredQueueSourceModel01.refused] at success; cases success
          | ok child =>
            simp only [walked]
            have frames := TransferDeferredCountFlush01.successful_walk_preserves_non_index_effects keys convert available height parent queued empty child walked
            constructor
            · change overlay parent.objects child.objects = parent.objects
              rw [frames.2.1]; rfl
            · change overlay parent.verifiable child.verifiable = parent.verifiable
              rw [frames.1]; rfl

theorem successful_actual_state_transfer_frames_original_pending_objects {O E A : Type}
    (io : TransferTakeCommitState01.Io O) (decode : O → Pending) (pendingKey : Nat)
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (deferred exclusive : Bool) (height : Option Nat) (parent returned : State O) (queued : List A)
    (success : (TransferTakeCommitState01.takeState io decode pendingKey keys convert available deferred exclusive height parent queued).returned = some returned) :
    returned.objects = parent.objects ∧ returned.verifiable = parent.verifiable := by
  obtain ⟨_, clean, _, same, _⟩ := TransferTakeCommitState01.whole_transfer_success_derives_sealed_flush_exclusive_and_exact_transferred_state
    io decode pendingKey keys convert available deferred exclusive height parent returned queued success
  rw [same]
  exact successful_concrete_flush_frames_pending_objects_without_count_premise keys convert available deferred exclusive height parent queued clean

def sealedState {O : Type} (encode : Pending → O) (decode : O → Pending) (project : Bytes → Nat)
    (state : State O) : State O :=
  applyCache state (TransferPendingSealSource01.sealOnce encode decode (project TransferNullifierObjectKeys01.nullifierBytes)
    ⟨state, (empty : Cache O Unit)⟩).cache

def FinalizationPendingFrame {O E A : Type} (io : TransferHostEndBlock01.Io O E A)
    (encode : Pending → O) (decode : O → Pending) (project : Bytes → Nat) : Prop :=
  ∀ height state queued,
    (io.endApplication height state queued).state.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      (sealedState encode decode project state).objects (project TransferNullifierObjectKeys01.nullifierBytes)

theorem whole_default_block_publication_commits_exact_global_inputs_under_finite_codec_and_finalization_field_contract {O E K X Tree A : Type}
    (encodeNative : TransferPendingFiniteCodec01.NativePending → O) (decodeNative : O → TransferPendingFiniteCodec01.NativePending)
    (typedRoundtrip : ∀ native, TransferPendingFiniteCodec01.restore (decodeNative (encodeNative native)) = TransferPendingFiniteCodec01.restore native)
    (project : Bytes → Nat) (injection : Function.Injective project)
    (requests : List (Request O E K X Tree A)) (parent : State O) (queued : List A) (final : State O × List A)
    (storedDefault : parent.objects (project TransferNullifierObjectKeys01.nullifierBytes) =
      some (TransferPendingFiniteCodec01.encode encodeNative TransferCurrentPendingReplay01.emptyPending))
    (walked : TransferBlockPendingSequence01.walk (TransferPendingFiniteCodec01.encode encodeNative)
      (TransferPendingFiniteCodec01.decode decodeNative) project parent queued requests = some final)
    (io : TransferEndToEnd01.Io O E A) (host : Host O) (height : Fin (2 ^ 64)) (root : Nat)
    (currentState : host.active = final.1)
    (projectedKeys : io.ending.project = project)
    (typedGetter : io.ending.decodePending = TransferPendingFiniteCodec01.decode decodeNative)
    (finalization : FinalizationPendingFrame io.ending (TransferPendingFiniteCodec01.encode encodeNative)
      (TransferPendingFiniteCodec01.decode decodeNative) project)
    (success : (TransferEndToEnd01.execute io host height final.2).root = some root) :
    ∃ frozen,
      frozen.insertions.accepted = allInputs requests ∧ (allInputs requests).Nodup ∧
      (allInputs requests).length ≤ TransferNullifierConsensusLimits01.blockCapacity ∧
      frozen.next.applicationRoot = some root ∧
      (TransferEndToEnd01.execute io host height final.2).host.phase = .idle ∧
      (TransferEndToEnd01.execute io host height final.2).host.writer = .ready frozen.next ∧
      (TransferEndToEnd01.execute io host height final.2).host.store.ready = true ∧
      (TransferEndToEnd01.execute io host height final.2).host.store.actualRoots = frozen.next.nullifiers.roots ∧
      (TransferEndToEnd01.execute io host height final.2).host.store.boundary = some frozen.next.nullifiers ∧
      frozen.next.nullifiers.roots.length = 16 ∧
      (TransferEndToEnd01.execute io host height final.2).host.store.healthy =
        (io.committing.writer.recoveryIo (TransferStatefulParticipantRecovery01.recoveryInput io.committing.writer
          (TransferEndToEnd01.sealed io host height final.2).host.store frozen)).healthyAfter := by
  have blockFacts := TransferReachablePendingBlock01.finite_codec_default_block_seals_exact_global_inputs
    encodeNative decodeNative typedRoundtrip project injection requests parent queued final storedDefault walked
  have exactOrder : (parentPending (TransferPendingFiniteCodec01.decode decodeNative) project
      (sealedState (TransferPendingFiniteCodec01.encode encodeNative) (TransferPendingFiniteCodec01.decode decodeNative) project final.1)).ordered = allInputs requests :=
    blockFacts.2.2.2.2.1
  obtain ⟨_, _, _, _, state, frozen, _, _, taken, accepted, _, _, appRoot, _, _, _, _, idle, _, ready, _, available, roots, stored, partitions, _, health, _⟩ :=
    TransferEndToEnd01.whole_returned_pipeline_derives_exact_inputs_same_boundary_and_actual_physical_recovery io host height final.2 root success
  have takeFrames := successful_actual_state_transfer_frames_original_pending_objects
    io.ending.transfer io.ending.decodePending (io.ending.project TransferNullifierObjectKeys01.nullifierBytes)
    io.ending.keys io.ending.convert io.ending.available io.ending.deferred io.ending.exclusive
    (io.ending.flushHeight (TransferHostEndBlock01.finalized io.ending host height final.2).state)
    (TransferHostEndBlock01.finalized io.ending host height final.2).state state
    (TransferHostEndBlock01.finalized io.ending host height final.2).queued taken
  have pendingSame : parentPending io.ending.decodePending io.ending.project state =
      parentPending (TransferPendingFiniteCodec01.decode decodeNative) project
        (sealedState (TransferPendingFiniteCodec01.encode encodeNative) (TransferPendingFiniteCodec01.decode decodeNative) project final.1) := by
    simp only [parentPending, TransferCurrentPendingReplay01.currentPending, apply_empty]
    rw [takeFrames.1, projectedKeys, typedGetter]
    have actualField := finalization height host.active final.2
    rw [currentState] at actualField
    simpa only [TransferHostEndBlock01.finalized, currentState] using congrArg
      (fun observed => match observed with | none => TransferCurrentPendingReplay01.emptyPending | some object => TransferPendingFiniteCodec01.decode decodeNative object) actualField
  refine ⟨frozen, ?_, blockFacts.2.2.2.2.2.1, blockFacts.2.2.2.2.2.2.1, appRoot, idle, ready, available, roots, stored, partitions, health⟩
  rw [accepted, pendingSame]; exact exactOrder

set_option pp.all true in
#check @successful_concrete_flush_frames_pending_objects_without_count_premise
#print axioms successful_concrete_flush_frames_pending_objects_without_count_premise
set_option pp.all true in
#check @successful_actual_state_transfer_frames_original_pending_objects
#print axioms successful_actual_state_transfer_frames_original_pending_objects
set_option pp.all true in
#check @sealedState
#print axioms sealedState
set_option pp.all true in
#check @FinalizationPendingFrame
#print axioms FinalizationPendingFrame
set_option pp.all true in
#check @whole_default_block_publication_commits_exact_global_inputs_under_finite_codec_and_finalization_field_contract
#print axioms whole_default_block_publication_commits_exact_global_inputs_under_finite_codec_and_finalization_field_contract
end ShielddSecurity.TransferGlobalCommitJoin01
