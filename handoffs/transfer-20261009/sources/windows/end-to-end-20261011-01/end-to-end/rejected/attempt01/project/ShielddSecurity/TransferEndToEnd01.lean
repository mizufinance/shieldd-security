import ShielddSecurity.TransferWriterRecoverCurrent01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferEndToEnd01
open TransferStateDelta
open TransferHostSealedCommit01 (Host)
open TransferWriterPrepareSource01 (Frozen CommitBoundary)
open TransferBlockPendingSequence01 (parentPending)

/-! Returned ordinary block pipeline, with each actual intermediate Host/Store
passed into the next source call. Success derives the guards and exact Frozen,
accepted vector, observed participant/recovery state and current poison health.
Captured-initial/native recovery equivalence is conditional on the explicit
forward partition contract; it is not hidden in a success callback. Recovery
and application reconstruction failures retain their actual prefix progress.
Finite pending codec, raw/proof snapshot coherence, ICS23/library semantics,
typed root/hash/serde, application component field frames, Arc/lock ownership,
async temporal ghost observations, signed height, OS durability and native
replay remain distinct interfaces. This is a closed theorem about the composed
source model; it is not full runtime certification. -/

structure Io (O E A : Type) where
  ending : TransferHostEndBlock01.Io O E A
  sealing : TransferHostSeal01.Io
  committing : TransferHostSealedCommit01.Io O

structure Outcome (O A : Type) where
  host : Host O
  queued : List A
  root : Option Nat

def ended {O E A : Type} (io : Io O E A) (host : Host O) (height : Fin (2 ^ 64)) (queued : List A) :=
  TransferHostEndBlock01.endBlock io.ending host height queued

def sealed {O E A : Type} (io : Io O E A) (host : Host O) (height : Fin (2 ^ 64)) (queued : List A) :=
  TransferHostSeal01.sealHost io.sealing (ended io host height queued).host

def execute {O E A : Type} (io : Io O E A) (host : Host O) (height : Fin (2 ^ 64)) (queued : List A) : Outcome O A :=
  let ending := ended io host height queued
  match ending.prepared with
  | none => ⟨ending.host, ending.queued, none⟩
  | some _ =>
    let sealing := sealed io host height queued
    match sealing.returned with
    | none => ⟨sealing.host, ending.queued, none⟩
    | some _ =>
      let committing := TransferHostSealedCommit01.commitSealed io.committing sealing.host
      ⟨committing.host, ending.queued, committing.root⟩

theorem whole_returned_pipeline_derives_exact_inputs_same_boundary_and_actual_physical_recovery {O E A : Type}
    (io : Io O E A) (host : Host O) (height : Fin (2 ^ 64)) (queued : List A) (root : Nat)
    (success : (execute io host height queued).root = some root) :
    host.phase = .inBlock ∧ io.ending.currentHeight host.active = some height.val ∧
    ∃ prepared sealedBoundary state frozen,
      (ended io host height queued).prepared = some prepared ∧
      (sealed io host height queued).returned = some sealedBoundary ∧
      (TransferHostEndBlock01.transferred io.ending host height queued).returned = some state ∧
      frozen.insertions.accepted = (parentPending io.ending.decodePending io.ending.project state).ordered ∧
      prepared = frozen.next ∧ sealedBoundary = frozen.next ∧ frozen.next.applicationRoot = some root ∧
      io.sealing.backend.writeLock = true ∧ io.sealing.backend.persistIntent frozen = true ∧
      (TransferStatefulParticipantRecovery01.participants io.committing.writer (sealed io host height queued).host.store frozen).completed = true ∧
      io.committing.writer.capacity frozen = true ∧
      (execute io host height queued).host.phase = .idle ∧
      (execute io host height queued).host.blockId = none ∧
      (execute io host height queued).host.writer = .ready frozen.next ∧
      (execute io host height queued).host.store =
        (TransferStatefulParticipantRecovery01.recovered io.committing.writer (sealed io host height queued).host.store frozen).store ∧
      (execute io host height queued).host.store.ready = true ∧
      (execute io host height queued).host.store.actualRoots = frozen.next.nullifiers.roots ∧
      (execute io host height queued).host.store.boundary = some frozen.next.nullifiers ∧
      frozen.next.nullifiers.roots.length = 16 ∧
      TransferBankRecovery.HistoryValid frozen.next.nullifiers
        (io.committing.writer.readHistory (TransferStatefulParticipantRecovery01.recoveryInput io.committing.writer (sealed io host height queued).host.store frozen)) ∧
      (execute io host height queued).host.store.healthy =
        (io.committing.writer.recoveryIo (TransferStatefulParticipantRecovery01.recoveryInput io.committing.writer (sealed io host height queued).host.store frozen)).healthyAfter ∧
      (execute io host height queued).host.active = TransferHostSealedCommit01.reset io.committing (execute io host height queued).host.store := by
  cases endCall : (ended io host height queued).prepared with
  | none => simp only [execute, endCall] at success; cases success
  | some prepared =>
    cases sealCall : (sealed io host height queued).returned with
    | none => simp only [execute, endCall, sealCall] at success; cases success
    | some sealedBoundary =>
      have commitSuccess : (TransferHostSealedCommit01.commitSealed io.committing (sealed io host height queued).host).root = some root := by
        simpa only [execute, endCall, sealCall] using success
      obtain ⟨inBlock, currentHeight, state, _, frozen, taken, _, _, _, preparedPhase, samePrepared, inputs, _⟩ :=
        TransferHostEndBlock01.whole_end_block_success_derives_actual_transfer_exact_pending_inputs_and_prepared_owner
          io.ending host height queued prepared endCall
      obtain ⟨_, sealFrozen, sealPrepared, locked, persisted, _, sealWriter, sameSealed, _⟩ :=
        TransferHostSeal01.successful_host_seal_derives_actual_lock_intent_same_frozen_and_observed_store
          io.sealing (ended io host height queued).host sealedBoundary sealCall
      have sameSealFrozen : frozen = sealFrozen := TransferWriterPrepareSource01.Phase.prepared.inj (preparedPhase.symm.trans sealPrepared)
      subst sealFrozen
      obtain ⟨_, boundary, commitFrozen, writerCall, appRoot, previousWriter, sameCommitted, idle, blockCleared, ready, physical, reset⟩ :=
        TransferHostSealedCommit01.returned_host_root_derives_same_ready_writer_and_actual_reset
          io.committing (sealed io host height queued).host root commitSuccess
      have sameCommitFrozen : frozen = commitFrozen := TransferWriterPrepareSource01.Phase.sealed.inj (sealWriter.symm.trans previousWriter)
      subst commitFrozen
      obtain ⟨other, oldPhase, completed, capacity, _, _, _⟩ :=
        TransferHostSealedCommit01.actual_writer_success_derives_sealed_completion_capacity_and_exact_physical_store
          io.committing.writer (sealed io host height queued).host.store (sealed io host height queued).host.writer boundary writerCall
      have sameOther : frozen = other := TransferWriterPrepareSource01.Phase.sealed.inj (sealWriter.symm.trans oldPhase)
      subst other
      obtain ⟨_, _, _, _, _, _, _, _, _, checks⟩ :=
        TransferStatefulParticipantRecovery01.whole_participant_success_derives_actual_temporal_inputs_and_recovery
          io.committing.writer (sealed io host height queued).host.store frozen completed
      have finalHost : (execute io host height queued).host = (TransferHostSealedCommit01.commitSealed io.committing (sealed io host height queued).host).host := by
        simp only [execute, endCall, sealCall]
      refine ⟨inBlock, currentHeight, prepared, sealedBoundary, state, frozen, endCall, sealCall, taken, inputs, samePrepared, sameSealed, ?_, locked, persisted, completed, capacity, ?_⟩
      · rw [← sameCommitted]; exact appRoot
      · rw [finalHost]
        rw [sameCommitted] at ready
        refine ⟨idle, blockCleared, ready, physical, ?_, ?_, ?_, checks.2.2.2.1, checks.2.2.2.2.1, ?_, reset⟩
        · rw [physical]; exact checks.1
        · rw [physical]; exact checks.2.1
        · rw [physical]; exact checks.2.2.1
        · rw [physical]; exact checks.2.2.2.2.2

theorem completion_store_equals_captured_initial_recovery_under_partition_frames
    (io : TransferStatefulParticipantRecovery01.Io) (store : TransferReadback.Store) (frozen : Frozen)
    (frames : TransferCapturedRecovery01.ForwardPartitionFrames (io.recoveryIo (TransferStatefulParticipantRecovery01.recoveryInput io store frozen))) :
    TransferStatefulParticipantRecovery01.recovered io store frozen =
      TransferCapturedRecovery01.recoverCaptured (TransferStatefulParticipantRecovery01.recoveryInput io store frozen)
        (io.recoveryIo (TransferStatefulParticipantRecovery01.recoveryInput io store frozen)) frozen.next.nullifiers
        (io.readIntent (TransferStatefulParticipantRecovery01.recoveryInput io store frozen))
        (io.readHistory (TransferStatefulParticipantRecovery01.recoveryInput io store frozen)) := by
  exact (TransferCapturedRecovery01.captured_recovery_reuses_original_result_under_explicit_partition_frames _ _ _ _ _ frames).symm

structure RollbackIo (O : Type) where
  recovering : TransferWriterRecoverCurrent01.Io O
  rebuild : TransferWriterRecoverCurrent01.Outcome → Option (State O)

structure RollbackOutcome (O : Type) where
  host : Host O
  deferredBatch : Bool
  succeeded : Bool

def rollback {O : Type} (io : RollbackIo O) (host : Host O) : RollbackOutcome O :=
  let recovered := TransferWriterRecoverCurrent01.recoverCurrent io.recovering host.store
  let current := {host with writer := recovered.phase, store := recovered.store}
  if recovered.succeeded = true then
    match io.rebuild recovered with
    | none => ⟨current, false, false⟩
    | some state => ⟨{current with phase := .idle, active := state, blockId := none}, true, true⟩
  else ⟨current, false, false⟩

theorem failed_current_recovery_preserves_host_fields_and_actual_writer_progress {O : Type}
    (io : RollbackIo O) (host : Host O)
    (failed : (TransferWriterRecoverCurrent01.recoverCurrent io.recovering host.store).succeeded = false) :
    (rollback io host).host.phase = host.phase ∧ (rollback io host).host.active = host.active ∧
      (rollback io host).host.blockId = host.blockId ∧
      (rollback io host).host.writer = (TransferWriterRecoverCurrent01.recoverCurrent io.recovering host.store).phase ∧
      (rollback io host).host.store = (TransferWriterRecoverCurrent01.recoverCurrent io.recovering host.store).store ∧
      (rollback io host).succeeded = false := by
  simp [rollback, failed]

theorem failed_application_rebuild_keeps_clean_recovery_progress_without_host_reset {O : Type}
    (io : RollbackIo O) (host : Host O)
    (clean : (TransferWriterRecoverCurrent01.recoverCurrent io.recovering host.store).succeeded = true)
    (failed : io.rebuild (TransferWriterRecoverCurrent01.recoverCurrent io.recovering host.store) = none) :
    (rollback io host).host.phase = host.phase ∧ (rollback io host).host.active = host.active ∧
      (rollback io host).host.blockId = host.blockId ∧
      (rollback io host).host.writer = (TransferWriterRecoverCurrent01.recoverCurrent io.recovering host.store).phase ∧
      (rollback io host).host.store = (TransferWriterRecoverCurrent01.recoverCurrent io.recovering host.store).store ∧
      (rollback io host).succeeded = false := by
  simp [rollback, clean, failed]

theorem returned_rollback_derives_actual_snapshot_recovery_and_actual_rebuilt_application {O : Type}
    (io : RollbackIo O) (host : Host O) (success : (rollback io host).succeeded = true) :
    ∃ state boundary,
      io.rebuild (TransferWriterRecoverCurrent01.recoverCurrent io.recovering host.store) = some state ∧
      TransferWriterRecoverCurrent01.selected io.recovering.snapshot = some boundary ∧
      (rollback io host).host.phase = .idle ∧ (rollback io host).host.blockId = none ∧
      (rollback io host).host.active = state ∧ (rollback io host).host.writer = .ready boundary ∧
      (rollback io host).host.store = (TransferWriterRecoverCurrent01.recovered io.recovering host.store boundary).store ∧
      (rollback io host).host.store.ready = true ∧
      (rollback io host).host.store.actualRoots = boundary.nullifiers.roots ∧
      (rollback io host).host.store.boundary = some boundary.nullifiers ∧
      (rollback io host).deferredBatch = true := by
  by_cases clean : (TransferWriterRecoverCurrent01.recoverCurrent io.recovering host.store).succeeded = true
  · cases rebuilt : io.rebuild (TransferWriterRecoverCurrent01.recoverCurrent io.recovering host.store) with
    | none => simp only [rollback, if_pos clean, rebuilt] at success; cases success
    | some state =>
      obtain ⟨boundary, selected, _, _, phase, physical, ready, roots, stored, _⟩ :=
        TransferWriterRecoverCurrent01.whole_current_recovery_success_derives_selected_boundary_actual_lock_and_observed_physical_state io.recovering host.store clean
      refine ⟨state, boundary, rebuilt, selected, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [rollback, if_pos clean, rebuilt]
      · simp only [rollback, if_pos clean, rebuilt]
      · simp only [rollback, if_pos clean, rebuilt]
      · simpa only [rollback, if_pos clean, rebuilt] using phase
      · simpa only [rollback, if_pos clean, rebuilt] using physical
      · simpa only [rollback, if_pos clean, rebuilt] using ready
      · simpa only [rollback, if_pos clean, rebuilt] using roots
      · simpa only [rollback, if_pos clean, rebuilt] using stored
      · simp only [rollback, if_pos clean, rebuilt]
  · simp only [rollback, if_neg clean] at success; cases success

set_option pp.all true in
#check @Io
#print axioms Io
set_option pp.all true in
#check @Outcome
#print axioms Outcome
set_option pp.all true in
#check @ended
#print axioms ended
set_option pp.all true in
#check @sealed
#print axioms sealed
set_option pp.all true in
#check @execute
#print axioms execute
set_option pp.all true in
#check @whole_returned_pipeline_derives_exact_inputs_same_boundary_and_actual_physical_recovery
#print axioms whole_returned_pipeline_derives_exact_inputs_same_boundary_and_actual_physical_recovery
set_option pp.all true in
#check @completion_store_equals_captured_initial_recovery_under_partition_frames
#print axioms completion_store_equals_captured_initial_recovery_under_partition_frames
set_option pp.all true in
#check @RollbackIo
#print axioms RollbackIo
set_option pp.all true in
#check @RollbackOutcome
#print axioms RollbackOutcome
set_option pp.all true in
#check @rollback
#print axioms rollback
set_option pp.all true in
#check @failed_current_recovery_preserves_host_fields_and_actual_writer_progress
#print axioms failed_current_recovery_preserves_host_fields_and_actual_writer_progress
set_option pp.all true in
#check @failed_application_rebuild_keeps_clean_recovery_progress_without_host_reset
#print axioms failed_application_rebuild_keeps_clean_recovery_progress_without_host_reset
set_option pp.all true in
#check @returned_rollback_derives_actual_snapshot_recovery_and_actual_rebuilt_application
#print axioms returned_rollback_derives_actual_snapshot_recovery_and_actual_rebuilt_application
end ShielddSecurity.TransferEndToEnd01
