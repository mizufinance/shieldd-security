import ShielddSecurity.TransferAuthenticatedBoundarySource01
import ShielddSecurity.TransferBankRecovery
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWriterRecoveryJoin01
open TransferReadback (Store Boundary)
open TransferWriterPrepareSource01 (Frozen Phase CommitBoundary)
open TransferWriterCommitSource01 (Backend participantsComplete commitWriter)

/-! Model composition of the actual-source writer call order with the original
independently qualified recovery kernel. Recovery produces observed physical
roots/health and checks retained history; the adapter reports only its returned
error status to the writer. Original recovery imports are reused, never replayed.
Native complete/recovery/rollback/partition frames/current poison state/locks,
typed boundary/sessions/IO and temporal state ownership remain correspondences.
The environment denotes the observed store at recovery invocation; mapping it
to prior native participant progress requires a separate state-threading proof.
Clean recovery preserves independently observed health, not assumed healthy.
Capacity failure follows Ready and does not imply physical rollback. -/

def recoverFor (store : Store) (io : TransferBankRecovery.Io)
    (intent : TransferBankRecovery.IntentRead) (history : TransferBankRecovery.HistoryRead) (frozen : Frozen) :
    TransferBankRecovery.Outcome :=
  TransferBankRecovery.recover store io frozen.next.nullifiers intent history

def installRecovery (backend : Backend) (store : Store) (io : TransferBankRecovery.Io)
    (intent : TransferBankRecovery.IntentRead) (history : TransferBankRecovery.HistoryRead) : Backend :=
  {backend with complete := fun frozen => decide ((recoverFor store io intent history frozen).error = none)}

theorem completed_source_participants_derive_recovery_boundary_history_and_observed_health
    (backend : Backend) (store : Store) (io : TransferBankRecovery.Io)
    (intent : TransferBankRecovery.IntentRead) (history : TransferBankRecovery.HistoryRead) (frozen : Frozen)
    (completed : participantsComplete (installRecovery backend store io intent history) frozen = some ()) :
    (recoverFor store io intent history frozen).error = none ∧
      (recoverFor store io intent history frozen).store.ready = true ∧
      (recoverFor store io intent history frozen).store.actualRoots = frozen.next.nullifiers.roots ∧
      (recoverFor store io intent history frozen).store.boundary = some frozen.next.nullifiers ∧
      frozen.next.nullifiers.roots.length = 16 ∧
      TransferBankRecovery.HistoryValid frozen.next.nullifiers history ∧
      (recoverFor store io intent history frozen).store.healthy = io.healthyAfter := by
  obtain ⟨_, _, _, _, _, _, _, reported⟩ :=
    TransferWriterCommitSource01.completed_participants_derives_every_prior_call_and_observed_root
      (installRecovery backend store io intent history) frozen completed
  have clean : (recoverFor store io intent history frozen).error = none := of_decide_eq_true reported
  have recovered := TransferBankRecovery.recovery_success_boundary store io frozen.next.nullifiers intent history
    (recoverFor store io intent history frozen) rfl clean
  exact ⟨clean, recovered⟩

theorem returned_source_commit_derives_same_ready_owner_and_observed_recovery_boundary
    (backend : Backend) (store : Store) (io : TransferBankRecovery.Io)
    (intent : TransferBankRecovery.IntentRead) (history : TransferBankRecovery.HistoryRead)
    (phase : Phase) (returned : CommitBoundary)
    (success : (commitWriter (installRecovery backend store io intent history) phase).returned = some returned) :
    ∃ frozen, phase = .sealed frozen ∧ returned = frozen.next ∧
      (commitWriter (installRecovery backend store io intent history) phase).phase = .ready returned ∧
      (recoverFor store io intent history frozen).error = none ∧
      (recoverFor store io intent history frozen).store.ready = true ∧
      (recoverFor store io intent history frozen).store.actualRoots = returned.nullifiers.roots ∧
      (recoverFor store io intent history frozen).store.boundary = some returned.nullifiers ∧
      returned.nullifiers.roots.length = 16 ∧
      (recoverFor store io intent history frozen).store.healthy = io.healthyAfter := by
  obtain ⟨frozen, sealed, completed, _, ready, same, _⟩ :=
    TransferWriterCommitSource01.successful_commit_derives_sealed_completed_capacity_and_same_frozen_boundary
      (installRecovery backend store io intent history) phase returned success
  have recovered := completed_source_participants_derive_recovery_boundary_history_and_observed_health
    backend store io intent history frozen completed
  subst returned
  exact ⟨frozen, sealed, rfl, ready, recovered.1, recovered.2.1, recovered.2.2.1,
    recovered.2.2.2.1, recovered.2.2.2.2.1, recovered.2.2.2.2.2.2⟩

theorem capacity_error_keeps_ready_owner_and_completed_observed_recovery
    (backend : Backend) (store : Store) (io : TransferBankRecovery.Io)
    (intent : TransferBankRecovery.IntentRead) (history : TransferBankRecovery.HistoryRead) (frozen : Frozen)
    (completed : participantsComplete (installRecovery backend store io intent history) frozen = some ())
    (capacity : backend.capacity frozen = false) :
    (commitWriter (installRecovery backend store io intent history) (.sealed frozen)).returned = none ∧
      (commitWriter (installRecovery backend store io intent history) (.sealed frozen)).phase = .ready frozen.next ∧
      (recoverFor store io intent history frozen).error = none ∧
      (recoverFor store io intent history frozen).store.boundary = some frozen.next.nullifiers ∧
      (recoverFor store io intent history frozen).store.actualRoots = frozen.next.nullifiers.roots := by
  have writer := TransferWriterCommitSource01.capacity_failure_occurs_after_ready_and_new_committed_boundary
    (installRecovery backend store io intent history) frozen completed capacity
  have recovered := completed_source_participants_derive_recovery_boundary_history_and_observed_health
    backend store io intent history frozen completed
  exact ⟨writer.2.1, writer.1, recovered.1, recovered.2.2.2.1, recovered.2.2.1⟩

theorem failed_recovery_prevents_participant_completion_and_blocks_owner_status {R : Type}
    (backend : Backend) (store : Store) (io : TransferBankRecovery.Io)
    (intent : TransferBankRecovery.IntentRead) (history : TransferBankRecovery.HistoryRead) (frozen : Frozen)
    (failed : (recoverFor store io intent history frozen).error ≠ none)
    (expected : CommitBoundary) (lookup : CommitBoundary → Option R) :
    participantsComplete (installRecovery backend store io intent history) frozen = none ∧
      TransferWriterSealDiscardSource01.ownerStatus
        (commitWriter (installRecovery backend store io intent history) (.sealed frozen)).phase expected lookup = none := by
  have unavailable : participantsComplete (installRecovery backend store io intent history) frozen = none := by
    cases returned : participantsComplete (installRecovery backend store io intent history) frozen with
    | none => rfl
    | some value =>
      cases value
      have recovered := completed_source_participants_derive_recovery_boundary_history_and_observed_health
        backend store io intent history frozen returned
      exact False.elim (failed recovered.1)
  exact ⟨unavailable, (TransferWriterCommitSource01.failed_before_participant_completion_interrupts_owner_status
    (installRecovery backend store io intent history) frozen unavailable expected lookup).2.2⟩

set_option pp.all true in
#check @recoverFor
#print axioms recoverFor
set_option pp.all true in
#check @installRecovery
#print axioms installRecovery
set_option pp.all true in
#check @completed_source_participants_derive_recovery_boundary_history_and_observed_health
#print axioms completed_source_participants_derive_recovery_boundary_history_and_observed_health
set_option pp.all true in
#check @returned_source_commit_derives_same_ready_owner_and_observed_recovery_boundary
#print axioms returned_source_commit_derives_same_ready_owner_and_observed_recovery_boundary
set_option pp.all true in
#check @capacity_error_keeps_ready_owner_and_completed_observed_recovery
#print axioms capacity_error_keeps_ready_owner_and_completed_observed_recovery
set_option pp.all true in
#check @failed_recovery_prevents_participant_completion_and_blocks_owner_status
#print axioms failed_recovery_prevents_participant_completion_and_blocks_owner_status
end ShielddSecurity.TransferWriterRecoveryJoin01
