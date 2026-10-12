import ShielddSecurity.TransferHostEndBlock01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferHostSeal01
open TransferHostSealedCommit01 (Host)
open TransferReadback (Store)
open TransferWriterPrepareSource01 (Frozen CommitBoundary)
open TransferWriterSealDiscardSource01 (SealBackend sealWriter)

/-! Source Host::seal_commit changes EndedBlock to CommitInterrupted before
actual writer seal; returned seal success alone reaches SealedBlock. The same
Frozen carries actual prepared accepted order. Independently observed Store
after native seal is threaded to Host, including failure progress/current
poison health; no desired ready/root/health or filesystem result is assumed.
Native after-call ghost correspondence, actual source intent/lock ownership,
typed boundary/Clone/library semantics and OS durability remain interfaces.
No negative-control, native or full certification inferred from this model. -/

structure Io where
  backend : SealBackend
  afterSeal : Store → TransferWriterPrepareSource01.Outcome → Store

structure Outcome (O : Type) where
  host : Host O
  returned : Option CommitBoundary

def sealHost {O : Type} (io : Io) (host : Host O) : Outcome O :=
  match host.phase with
  | .endedBlock =>
    let result := sealWriter io.backend host.writer
    let current := io.afterSeal host.store result
    match result.returned with
    | none => ⟨{host with phase := .commitInterrupted, writer := result.phase, store := current}, none⟩
    | some boundary => ⟨{host with phase := .sealedBlock, writer := result.phase, store := current}, some boundary⟩
  | _ => ⟨host, none⟩

theorem successful_host_seal_derives_actual_lock_intent_same_frozen_and_observed_store {O : Type}
    (io : Io) (host : Host O) (boundary : CommitBoundary)
    (success : (sealHost io host).returned = some boundary) :
    host.phase = .endedBlock ∧ ∃ frozen,
      host.writer = .prepared frozen ∧ io.backend.writeLock = true ∧ io.backend.persistIntent frozen = true ∧
      (sealHost io host).host.phase = .sealedBlock ∧ (sealHost io host).host.writer = .sealed frozen ∧
      boundary = frozen.next ∧
      (sealHost io host).host.store = io.afterSeal host.store (sealWriter io.backend host.writer) ∧
      (sealHost io host).host.active = host.active ∧ (sealHost io host).host.blockId = host.blockId := by
  cases phase : host.phase <;> try (simp only [sealHost, phase] at success; cases success)
  cases call : (sealWriter io.backend host.writer).returned with
  | none => simp only [sealHost, phase, call] at success; cases success
  | some returned =>
    have same : returned = boundary := Option.some.inj (by simpa only [sealHost, phase, call] using success)
    subst returned
    obtain ⟨frozen, prepared, locked, persisted, sealed, returnedExact⟩ :=
      TransferWriterSealDiscardSource01.successful_seal_derives_prepared_lock_intent_and_same_frozen_boundary
        io.backend host.writer boundary call
    refine ⟨rfl, frozen, prepared, locked, persisted, ?_, ?_, returnedExact, ?_, ?_, ?_⟩
    · simp only [sealHost, phase, call]
    · simpa only [sealHost, phase, call] using sealed
    · simp only [sealHost, phase, call]
    · simp only [sealHost, phase, call]
    · simp only [sealHost, phase, call]

theorem failed_actual_writer_seal_keeps_host_interrupted_and_observed_progress {O : Type}
    (io : Io) (host : Host O) (ended : host.phase = .endedBlock)
    (failed : (sealWriter io.backend host.writer).returned = none) :
    sealHost io host =
      ⟨{host with phase := .commitInterrupted, writer := (sealWriter io.backend host.writer).phase, store := io.afterSeal host.store (sealWriter io.backend host.writer)}, none⟩ := by
  simp only [sealHost, ended, failed]

theorem other_host_phase_refuses_seal_without_changing_state {O : Type}
    (io : Io) (host : Host O) (unended : host.phase ≠ .endedBlock) : sealHost io host = ⟨host, none⟩ := by
  cases phase : host.phase with
  | idle => simp only [sealHost, phase]
  | initializedGenesis => simp only [sealHost, phase]
  | initializedCheckpointGenesis => simp only [sealHost, phase]
  | inBlock => simp only [sealHost, phase]
  | endedBlock => exact False.elim (unended phase)
  | sealedBlock => simp only [sealHost, phase]
  | commitInterrupted => simp only [sealHost, phase]

theorem actual_end_block_then_seal_keeps_exact_transferred_pending_order {O E A : Type}
    (endIo : TransferHostEndBlock01.Io O E A) (host : Host O) (height : Fin (2 ^ 64)) (queued : List A)
    (prepared : CommitBoundary) (endSuccess : (TransferHostEndBlock01.endBlock endIo host height queued).prepared = some prepared)
    (sealIo : Io) (sealed : CommitBoundary)
    (sealSuccess : (sealHost sealIo (TransferHostEndBlock01.endBlock endIo host height queued).host).returned = some sealed) :
    ∃ state frozen,
      (TransferHostEndBlock01.transferred endIo host height queued).returned = some state ∧
      frozen.insertions.accepted = (TransferBlockPendingSequence01.parentPending endIo.decodePending endIo.project state).ordered ∧
      (sealHost sealIo (TransferHostEndBlock01.endBlock endIo host height queued).host).host.phase = .sealedBlock ∧
      (sealHost sealIo (TransferHostEndBlock01.endBlock endIo host height queued).host).host.writer = .sealed frozen ∧
      sealed = frozen.next ∧ prepared = frozen.next := by
  obtain ⟨_, _, state, _, frozen, taken, _, _, _, preparedPhase, samePrepared, inputs, _⟩ :=
    TransferHostEndBlock01.whole_end_block_success_derives_actual_transfer_exact_pending_inputs_and_prepared_owner
      endIo host height queued prepared endSuccess
  obtain ⟨_, other, previous, _, _, sealedPhase, sameWriter, sameBoundary, _⟩ :=
    successful_host_seal_derives_actual_lock_intent_same_frozen_and_observed_store
      sealIo (TransferHostEndBlock01.endBlock endIo host height queued).host sealed sealSuccess
  have sameFrozen : frozen = other := TransferWriterPrepareSource01.Phase.prepared.inj (preparedPhase.symm.trans previous)
  subst other
  exact ⟨state, frozen, taken, inputs, sealedPhase, sameWriter, sameBoundary, samePrepared⟩

set_option pp.all true in
#check @Io
#print axioms Io
set_option pp.all true in
#check @Outcome
#print axioms Outcome
set_option pp.all true in
#check @sealHost
#print axioms sealHost
set_option pp.all true in
#check @successful_host_seal_derives_actual_lock_intent_same_frozen_and_observed_store
#print axioms successful_host_seal_derives_actual_lock_intent_same_frozen_and_observed_store
set_option pp.all true in
#check @failed_actual_writer_seal_keeps_host_interrupted_and_observed_progress
#print axioms failed_actual_writer_seal_keeps_host_interrupted_and_observed_progress
set_option pp.all true in
#check @other_host_phase_refuses_seal_without_changing_state
#print axioms other_host_phase_refuses_seal_without_changing_state
set_option pp.all true in
#check @actual_end_block_then_seal_keeps_exact_transferred_pending_order
#print axioms actual_end_block_then_seal_keeps_exact_transferred_pending_order
end ShielddSecurity.TransferHostSeal01
