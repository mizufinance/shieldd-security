import ShielddSecurity.TransferWriterSealDiscardSource01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWriterCommitSource01
open TransferWriterPrepareSource01 (CommitBoundary Frozen Phase Outcome)
open TransferWriterSealDiscardSource01 (committed ownerStatus)

/-! Exact source writer commit ordering and phase projection. A Sealed proposal
is replaced by Interrupted before version/locks/NOMT/application/root/recovery
checks. Only participant completion sets Ready; capacity is checked afterward,
so returned error can coexist with Ready and a new committed boundary.
Each callback denotes an independently observed native result. Physical roots,
partial commit progress, durability, lock health, batch/version/Clone/native
correspondence and recovery/reader semantics remain separate interfaces.
No error implies physical rollback. No native/control/full certification. -/

structure Backend where
  applicationUnchanged : Frozen → Bool
  nullifierLock : Bool
  commitNullifiers : Frozen → Bool
  commitApplication : Frozen → Option Nat
  completeLock : Bool
  complete : Frozen → Bool
  capacity : Frozen → Bool

def participantsComplete (backend : Backend) (frozen : Frozen) : Option Unit :=
  if backend.applicationUnchanged frozen = true then
    if backend.nullifierLock = true then
      if backend.commitNullifiers frozen = true then
        (backend.commitApplication frozen).bind fun actualRoot =>
          if some actualRoot = frozen.next.applicationRoot then
            if backend.completeLock = true then
              if backend.complete frozen = true then some () else none
            else none
          else none
      else none
    else none
  else none

def commitWriter (backend : Backend) (phase : Phase) : Outcome :=
  match phase with
  | .sealed frozen =>
    if participantsComplete backend frozen = some () then
      ⟨.ready frozen.next, if backend.capacity frozen = true then some frozen.next else none⟩
    else ⟨.interrupted, none⟩
  | _ => ⟨phase, none⟩

theorem wrong_phase_refuses_commit_and_retains_original_phase (backend : Backend) (phase : Phase)
    (unsealed : ∀ frozen, phase ≠ .sealed frozen) :
    (commitWriter backend phase).phase = phase ∧ (commitWriter backend phase).returned = none := by
  cases phase with
  | ready _ => exact ⟨rfl, rfl⟩
  | prepared _ => exact ⟨rfl, rfl⟩
  | sealed frozen => exact False.elim (unsealed frozen rfl)
  | interrupted => exact ⟨rfl, rfl⟩

theorem completed_participants_derives_every_prior_call_and_observed_root (backend : Backend) (frozen : Frozen)
    (success : participantsComplete backend frozen = some ()) :
    backend.applicationUnchanged frozen = true ∧ backend.nullifierLock = true ∧ backend.commitNullifiers frozen = true ∧
      ∃ actualRoot, backend.commitApplication frozen = some actualRoot ∧ some actualRoot = frozen.next.applicationRoot ∧
        backend.completeLock = true ∧ backend.complete frozen = true := by
  by_cases version : backend.applicationUnchanged frozen = true
  · by_cases locked : backend.nullifierLock = true
    · by_cases nullifiers : backend.commitNullifiers frozen = true
      · cases application : backend.commitApplication frozen with
        | none => simp only [participantsComplete, if_pos version, if_pos locked, if_pos nullifiers, application, Option.bind_none] at success; contradiction
        | some actualRoot =>
          by_cases root : some actualRoot = frozen.next.applicationRoot
          · by_cases completionLock : backend.completeLock = true
            · by_cases complete : backend.complete frozen = true
              · exact ⟨version, locked, nullifiers, actualRoot, rfl, root, completionLock, complete⟩
              · simp only [participantsComplete, if_pos version, if_pos locked, if_pos nullifiers, application, Option.bind_some, if_pos root, if_pos completionLock, if_neg complete] at success; contradiction
            · simp only [participantsComplete, if_pos version, if_pos locked, if_pos nullifiers, application, Option.bind_some, if_pos root, if_neg completionLock] at success; contradiction
          · simp only [participantsComplete, if_pos version, if_pos locked, if_pos nullifiers, application, Option.bind_some, if_neg root] at success; contradiction
      · simp only [participantsComplete, if_pos version, if_pos locked, if_neg nullifiers] at success; contradiction
    · simp only [participantsComplete, if_pos version, if_neg locked] at success; contradiction
  · simp only [participantsComplete, if_neg version] at success; contradiction

theorem failed_before_participant_completion_interrupts_owner_status {R : Type} (backend : Backend) (frozen : Frozen)
    (failed : participantsComplete backend frozen = none) (expected : CommitBoundary) (lookup : CommitBoundary → Option R) :
    (commitWriter backend (.sealed frozen)).phase = .interrupted ∧
      (commitWriter backend (.sealed frozen)).returned = none ∧
      ownerStatus (commitWriter backend (.sealed frozen)).phase expected lookup = none := by
  have refused : participantsComplete backend frozen ≠ some () := by intro impossible; rw [failed] at impossible; contradiction
  have phase : (commitWriter backend (.sealed frozen)).phase = .interrupted := by simp only [commitWriter, if_neg refused]
  have returned : (commitWriter backend (.sealed frozen)).returned = none := by simp only [commitWriter, if_neg refused]
  exact ⟨phase, returned, by simpa only [phase] using TransferWriterSealDiscardSource01.interrupted_owner_status_unavailable expected lookup⟩

theorem capacity_failure_occurs_after_ready_and_new_committed_boundary (backend : Backend) (frozen : Frozen)
    (completed : participantsComplete backend frozen = some ()) (capacity : backend.capacity frozen = false) :
    (commitWriter backend (.sealed frozen)).phase = .ready frozen.next ∧
      (commitWriter backend (.sealed frozen)).returned = none ∧
      committed (commitWriter backend (.sealed frozen)).phase = some frozen.next := by
  have ready : (commitWriter backend (.sealed frozen)).phase = .ready frozen.next := by simp only [commitWriter, if_pos completed]
  have returned : (commitWriter backend (.sealed frozen)).returned = none := by
    simp only [commitWriter, if_pos completed, capacity, Bool.false_eq_true, if_false]
  exact ⟨ready, returned, by simp only [ready, committed]⟩

theorem successful_commit_derives_sealed_completed_capacity_and_same_frozen_boundary (backend : Backend) (phase : Phase)
    (returned : CommitBoundary) (success : (commitWriter backend phase).returned = some returned) :
    ∃ frozen, phase = .sealed frozen ∧ participantsComplete backend frozen = some () ∧ backend.capacity frozen = true ∧
      (commitWriter backend phase).phase = .ready frozen.next ∧ returned = frozen.next ∧
      committed (commitWriter backend phase).phase = some returned := by
  cases phase with
  | ready _ => simp only [commitWriter] at success; contradiction
  | prepared _ => simp only [commitWriter] at success; contradiction
  | interrupted => simp only [commitWriter] at success; contradiction
  | sealed frozen =>
    by_cases completed : participantsComplete backend frozen = some ()
    · by_cases capacity : backend.capacity frozen = true
      · have returnedExact : frozen.next = returned := Option.some.inj (by simpa only [commitWriter, if_pos completed, if_pos capacity] using success)
        have ready : (commitWriter backend (.sealed frozen)).phase = .ready frozen.next := by simp only [commitWriter, if_pos completed]
        exact ⟨frozen, rfl, completed, capacity, ready, returnedExact.symm, by simp only [ready, committed, returnedExact]⟩
      · simp only [commitWriter, if_pos completed, if_neg capacity] at success; contradiction
    · simp only [commitWriter, if_neg completed] at success; contradiction

theorem whole_prepare_seal_commit_retains_exact_accepted_inputs {O : Type}
    (prepareBackend : TransferWriterPrepareSource01.Backend O) (phase : Phase) (state : TransferStateDelta.State O)
    (height : Fin (2 ^ 64)) (blockId accepted : List Nat) (preparedReturned : CommitBoundary)
    (prepareSuccess : (TransferWriterPrepareSource01.prepareWriter prepareBackend phase state height blockId accepted).returned = some preparedReturned)
    (sealBackend : TransferWriterSealDiscardSource01.SealBackend) (sealedReturned : CommitBoundary)
    (sealSuccess : (TransferWriterSealDiscardSource01.sealWriter sealBackend (TransferWriterPrepareSource01.prepareWriter prepareBackend phase state height blockId accepted).phase).returned = some sealedReturned)
    (commitBackend : Backend) (committedReturned : CommitBoundary)
    (commitSuccess : (commitWriter commitBackend (TransferWriterSealDiscardSource01.sealWriter sealBackend
      (TransferWriterPrepareSource01.prepareWriter prepareBackend phase state height blockId accepted).phase).phase).returned = some committedReturned) :
    ∃ frozen,
      (commitWriter commitBackend (TransferWriterSealDiscardSource01.sealWriter sealBackend
        (TransferWriterPrepareSource01.prepareWriter prepareBackend phase state height blockId accepted).phase).phase).phase = .ready frozen.next ∧
      frozen.insertions.accepted = accepted ∧ committedReturned = preparedReturned ∧
      participantsComplete commitBackend frozen = some () ∧ commitBackend.capacity frozen = true := by
  obtain ⟨frozen, sealedPhase, inputs, _, _, _⟩ :=
    TransferWriterSealDiscardSource01.whole_successful_prepare_then_seal_retains_exact_frozen_inputs
      prepareBackend phase state height blockId accepted preparedReturned prepareSuccess sealBackend sealedReturned sealSuccess
  have commitCall : (commitWriter commitBackend (.sealed frozen)).returned = some committedReturned := by simpa only [sealedPhase] using commitSuccess
  obtain ⟨other, initialPhase, completed, capacity, ready, returnedCommit, _⟩ :=
    successful_commit_derives_sealed_completed_capacity_and_same_frozen_boundary commitBackend (.sealed frozen) committedReturned commitCall
  have same : frozen = other := Phase.sealed.inj initialPhase
  subst other
  obtain ⟨prepared, _, preparedPhase, preparedExact, _, _, _⟩ :=
    TransferWriterPrepareSource01.successful_writer_derives_prepared_phase_exact_inputs_and_observed_root
      prepareBackend phase state height blockId accepted preparedReturned prepareSuccess
  have sealedCall : (TransferWriterSealDiscardSource01.sealWriter sealBackend (.prepared prepared)).returned = some sealedReturned := by simpa only [preparedPhase] using sealSuccess
  obtain ⟨sealed, started, _, _, sameSealedPhase, _⟩ :=
    TransferWriterSealDiscardSource01.successful_seal_derives_prepared_lock_intent_and_same_frozen_boundary sealBackend (.prepared prepared) sealedReturned sealedCall
  have preparedSame : prepared = sealed := Phase.prepared.inj started
  subst sealed
  have phaseSame : Phase.sealed frozen = Phase.sealed prepared := by
    rw [← sealedPhase]
    simpa only [preparedPhase] using sameSealedPhase
  have frozenSame : frozen = prepared := Phase.sealed.inj phaseSame
  have boundarySame : committedReturned = preparedReturned := by rw [returnedCommit, frozenSame]; exact preparedExact.symm
  refine ⟨frozen, ?_, inputs, boundarySame, completed, capacity⟩
  simpa only [sealedPhase] using ready

set_option pp.all true in
#check @Backend
#print axioms Backend
set_option pp.all true in
#check @participantsComplete
#print axioms participantsComplete
set_option pp.all true in
#check @commitWriter
#print axioms commitWriter
set_option pp.all true in
#check @wrong_phase_refuses_commit_and_retains_original_phase
#print axioms wrong_phase_refuses_commit_and_retains_original_phase
set_option pp.all true in
#check @completed_participants_derives_every_prior_call_and_observed_root
#print axioms completed_participants_derives_every_prior_call_and_observed_root
set_option pp.all true in
#check @failed_before_participant_completion_interrupts_owner_status
#print axioms failed_before_participant_completion_interrupts_owner_status
set_option pp.all true in
#check @capacity_failure_occurs_after_ready_and_new_committed_boundary
#print axioms capacity_failure_occurs_after_ready_and_new_committed_boundary
set_option pp.all true in
#check @successful_commit_derives_sealed_completed_capacity_and_same_frozen_boundary
#print axioms successful_commit_derives_sealed_completed_capacity_and_same_frozen_boundary
set_option pp.all true in
#check @whole_prepare_seal_commit_retains_exact_accepted_inputs
#print axioms whole_prepare_seal_commit_retains_exact_accepted_inputs
end ShielddSecurity.TransferWriterCommitSource01
