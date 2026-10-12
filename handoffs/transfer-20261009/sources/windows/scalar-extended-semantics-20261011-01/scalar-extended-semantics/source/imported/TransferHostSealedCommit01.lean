import ShielddSecurity.TransferTakeCommitState01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferHostSealedCommit01
open TransferReadback (Store)
open TransferWriterPrepareSource01 (Phase Frozen CommitBoundary)
open TransferStateDelta (State Bytes)

/-! The ordinary finalized-block branch of Host::commit. Host becomes
CommitInterrupted before the actual state-threaded writer call. A returned
writer error retains its actual writer phase/physical progress, including
Ready after a capacity error. After writer success, reset installs the observed
latest snapshot/current reader, block identity is cleared and Host becomes Idle
before the final optional application-root extraction. Actual participant
success already derives a present application root; the final missing-root
guard is unreachable under that source contract. Genesis preparation/sealing is a
separate source branch. Native Host/Arc/reader/snapshot/storage/typed root bytes,
concurrency/library/ownership, concrete proof correspondence and durability
remain explicit; no native/control/full certification from these branches. -/

inductive HostPhase where
  | idle | initializedGenesis | initializedCheckpointGenesis | inBlock
  | endedBlock | sealedBlock | commitInterrupted

structure Host (O : Type) where
  phase : HostPhase
  writer : Phase
  active : State O
  blockId : Option Bytes
  store : Store

structure Io (O : Type) where
  writer : TransferStatefulParticipantRecovery01.Io
  latestSnapshot : Store → State O
  readerKey : Nat
  reader : Store → O

structure Outcome (O : Type) where
  host : Host O
  root : Option Nat

def reset {O : Type} (io : Io O) (store : Store) : State O :=
  ⟨(io.latestSnapshot store).verifiable, (io.latestSnapshot store).nonverifiable,
    fun key => if key = io.readerKey then some (io.reader store) else none⟩

def commitSealed {O : Type} (io : Io O) (host : Host O) : Outcome O :=
  match host.phase with
  | .sealedBlock =>
    let result := TransferStatefulParticipantRecovery01.commitWriter io.writer host.store host.writer
    match result.returned with
    | none => ⟨{host with phase := .commitInterrupted, writer := result.phase, store := result.store}, none⟩
    | some committed =>
      ⟨{host with phase := .idle, writer := result.phase, active := reset io result.store, blockId := none, store := result.store}, committed.applicationRoot⟩
  | _ => ⟨host, none⟩

theorem actual_writer_success_derives_sealed_completion_capacity_and_exact_physical_store
    (io : TransferStatefulParticipantRecovery01.Io) (store : Store) (phase : Phase) (returned : CommitBoundary)
    (success : (TransferStatefulParticipantRecovery01.commitWriter io store phase).returned = some returned) :
    ∃ frozen, phase = .sealed frozen ∧
      (TransferStatefulParticipantRecovery01.participants io store frozen).completed = true ∧
      io.capacity frozen = true ∧ returned = frozen.next ∧
      (TransferStatefulParticipantRecovery01.commitWriter io store phase).phase = .ready returned ∧
      (TransferStatefulParticipantRecovery01.commitWriter io store phase).store =
        (TransferStatefulParticipantRecovery01.recovered io store frozen).store := by
  cases phase with
  | ready _ => simp only [TransferStatefulParticipantRecovery01.commitWriter] at success; cases success
  | prepared _ => simp only [TransferStatefulParticipantRecovery01.commitWriter] at success; cases success
  | interrupted => simp only [TransferStatefulParticipantRecovery01.commitWriter] at success; cases success
  | sealed frozen =>
    by_cases completed : (TransferStatefulParticipantRecovery01.participants io store frozen).completed = true
    · by_cases capacity : io.capacity frozen = true
      · have same : returned = frozen.next := (Option.some.inj (by
          simpa only [TransferStatefulParticipantRecovery01.commitWriter, if_pos completed, if_pos capacity] using success)).symm
        obtain ⟨_, _, _, _, _, _, _, _, physical, _⟩ :=
          TransferStatefulParticipantRecovery01.whole_participant_success_derives_actual_temporal_inputs_and_recovery io store frozen completed
        refine ⟨frozen, rfl, completed, capacity, same, ?_, ?_⟩
        · simp only [TransferStatefulParticipantRecovery01.commitWriter, if_pos completed, same]
        · simpa only [TransferStatefulParticipantRecovery01.commitWriter, if_pos completed] using physical
      · simp only [TransferStatefulParticipantRecovery01.commitWriter, if_pos completed, if_neg capacity] at success; cases success
    · simp only [TransferStatefulParticipantRecovery01.commitWriter, if_neg completed] at success; cases success

theorem other_host_phase_refuses_this_ordinary_branch {O : Type} (io : Io O) (host : Host O)
    (unsealed : host.phase ≠ .sealedBlock) : commitSealed io host = ⟨host, none⟩ := by
  cases phase : host.phase with
  | idle => simp only [commitSealed, phase]
  | initializedGenesis => simp only [commitSealed, phase]
  | initializedCheckpointGenesis => simp only [commitSealed, phase]
  | inBlock => simp only [commitSealed, phase]
  | endedBlock => simp only [commitSealed, phase]
  | sealedBlock => exact False.elim (unsealed phase)
  | commitInterrupted => simp only [commitSealed, phase]

theorem actual_writer_error_interrupts_host_and_retains_observed_writer_and_store {O : Type}
    (io : Io O) (host : Host O) (sealedHost : host.phase = .sealedBlock)
    (failed : (TransferStatefulParticipantRecovery01.commitWriter io.writer host.store host.writer).returned = none) :
    (commitSealed io host).host.phase = .commitInterrupted ∧
      (commitSealed io host).host.writer = (TransferStatefulParticipantRecovery01.commitWriter io.writer host.store host.writer).phase ∧
      (commitSealed io host).host.store = (TransferStatefulParticipantRecovery01.commitWriter io.writer host.store host.writer).store ∧
      (commitSealed io host).host.active = host.active ∧ (commitSealed io host).host.blockId = host.blockId ∧
      (commitSealed io host).root = none := by
  simp [commitSealed, sealedHost, failed]

theorem capacity_error_keeps_host_interrupted_but_writer_ready_with_completed_physical_state {O : Type}
    (io : Io O) (host : Host O) (frozen : Frozen) (sealedHost : host.phase = .sealedBlock)
    (sealedWriter : host.writer = .sealed frozen)
    (completed : (TransferStatefulParticipantRecovery01.participants io.writer host.store frozen).completed = true)
    (capacity : io.writer.capacity frozen = false) :
    (commitSealed io host).host.phase = .commitInterrupted ∧
      (commitSealed io host).host.writer = .ready frozen.next ∧
      (commitSealed io host).host.store = (TransferStatefulParticipantRecovery01.recovered io.writer host.store frozen).store ∧
      (commitSealed io host).host.active = host.active ∧ (commitSealed io host).host.blockId = host.blockId := by
  have writer := TransferStatefulParticipantRecovery01.capacity_failure_keeps_ready_owner_and_exact_completed_physical_store
    io.writer host.store frozen completed capacity
  have failed : (TransferStatefulParticipantRecovery01.commitWriter io.writer host.store host.writer).returned = none := by
    rw [sealedWriter]; exact writer.2.1
  have hostResult := actual_writer_error_interrupts_host_and_retains_observed_writer_and_store io host sealedHost failed
  exact ⟨hostResult.1, by rw [hostResult.2.1, sealedWriter]; exact writer.1,
    by rw [hostResult.2.2.1, sealedWriter]; exact writer.2.2, hostResult.2.2.2.1, hostResult.2.2.2.2.1⟩

theorem returned_host_root_derives_same_ready_writer_and_actual_reset {O : Type}
    (io : Io O) (host : Host O) (root : Nat) (success : (commitSealed io host).root = some root) :
    host.phase = .sealedBlock ∧ ∃ boundary frozen,
      (TransferStatefulParticipantRecovery01.commitWriter io.writer host.store host.writer).returned = some boundary ∧
      boundary.applicationRoot = some root ∧ host.writer = .sealed frozen ∧ boundary = frozen.next ∧
      (commitSealed io host).host.phase = .idle ∧ (commitSealed io host).host.blockId = none ∧
      (commitSealed io host).host.writer = .ready boundary ∧
      (commitSealed io host).host.store = (TransferStatefulParticipantRecovery01.recovered io.writer host.store frozen).store ∧
      (commitSealed io host).host.active = reset io (commitSealed io host).host.store := by
  cases phase : host.phase <;> try (simp only [commitSealed, phase] at success; cases success)
  cases returned : (TransferStatefulParticipantRecovery01.commitWriter io.writer host.store host.writer).returned with
  | none => simp only [commitSealed, phase, returned] at success; cases success
  | some boundary =>
    have rootSame : boundary.applicationRoot = some root := by simpa only [commitSealed, phase, returned] using success
    obtain ⟨frozen, sealed, _, _, same, ready, physical⟩ :=
      actual_writer_success_derives_sealed_completion_capacity_and_exact_physical_store io.writer host.store host.writer boundary returned
    refine ⟨rfl, boundary, frozen, rfl, rootSame, sealed, same, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [commitSealed, phase, returned]
    · simp only [commitSealed, phase, returned]
    · simpa only [commitSealed, phase, returned] using ready
    · simpa only [commitSealed, phase, returned] using physical
    · simp only [commitSealed, phase, returned]

theorem source_writer_success_guarantees_final_host_root_extraction {O : Type}
    (io : Io O) (host : Host O) (boundary : CommitBoundary) (sealedHost : host.phase = .sealedBlock)
    (returned : (TransferStatefulParticipantRecovery01.commitWriter io.writer host.store host.writer).returned = some boundary) :
    ∃ root, boundary.applicationRoot = some root ∧ (commitSealed io host).root = some root ∧
      (commitSealed io host).host.phase = .idle ∧
      (commitSealed io host).host.blockId = none ∧
      (commitSealed io host).host.active = reset io (commitSealed io host).host.store := by
  obtain ⟨frozen, _, completed, _, same, _, _⟩ :=
    actual_writer_success_derives_sealed_completion_capacity_and_exact_physical_store io.writer host.store host.writer boundary returned
  obtain ⟨_, _, _, root, _, rootMatch, _⟩ :=
    TransferStatefulParticipantRecovery01.whole_participant_success_derives_actual_temporal_inputs_and_recovery io.writer host.store frozen completed
  have present : boundary.applicationRoot = some root := by rw [same]; exact rootMatch.symm
  refine ⟨root, present, ?_, ?_, ?_, ?_⟩
  · simp only [commitSealed, sealedHost, returned, present]
  · simp only [commitSealed, sealedHost, returned]
  · simp only [commitSealed, sealedHost, returned]
  · simp only [commitSealed, sealedHost, returned]

set_option pp.all true in
#check @HostPhase
#print axioms HostPhase
set_option pp.all true in
#check @Host
#print axioms Host
set_option pp.all true in
#check @Io
#print axioms Io
set_option pp.all true in
#check @Outcome
#print axioms Outcome
set_option pp.all true in
#check @reset
#print axioms reset
set_option pp.all true in
#check @commitSealed
#print axioms commitSealed
set_option pp.all true in
#check @actual_writer_success_derives_sealed_completion_capacity_and_exact_physical_store
#print axioms actual_writer_success_derives_sealed_completion_capacity_and_exact_physical_store
set_option pp.all true in
#check @other_host_phase_refuses_this_ordinary_branch
#print axioms other_host_phase_refuses_this_ordinary_branch
set_option pp.all true in
#check @actual_writer_error_interrupts_host_and_retains_observed_writer_and_store
#print axioms actual_writer_error_interrupts_host_and_retains_observed_writer_and_store
set_option pp.all true in
#check @capacity_error_keeps_host_interrupted_but_writer_ready_with_completed_physical_state
#print axioms capacity_error_keeps_host_interrupted_but_writer_ready_with_completed_physical_state
set_option pp.all true in
#check @returned_host_root_derives_same_ready_writer_and_actual_reset
#print axioms returned_host_root_derives_same_ready_writer_and_actual_reset
set_option pp.all true in
#check @source_writer_success_guarantees_final_host_root_extraction
#print axioms source_writer_success_guarantees_final_host_root_extraction
end ShielddSecurity.TransferHostSealedCommit01
