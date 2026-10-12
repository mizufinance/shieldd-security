import ShielddSecurity.TransferStatefulStoreCommit01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferStatefulParticipantRecovery01
open TransferReadback (Store)
open TransferWriterPrepareSource01 (Frozen Phase CommitBoundary)
open TransferStatefulStoreCommit01 (Physical observe)

/-! Actual writer participant order with temporal physical state threading.
NOMT commit output is the input to application commit; its physical observation
is the input to the later completion lock; the lock observation is exactly the
Store input to recovery. No separate desired recovery Store is supplied.
Physical observations are ghosts of independently observed roots/current poison,
not new native calls, and frame the writer-owned ready and boundary fields.
Original recovery kernel remains scoped by its original native partition-frame
and captured-initial-root correspondence interfaces. Returned recovery success
does not infer healthy, durability, authenticated application contents or the
native ICS23/storage/Host/lock/ownership/library implementation contracts. -/

structure ApplicationResult where
  physical : Physical
  root : Option Nat

structure LockResult where
  physical : Physical
  acquired : Bool

structure Io where
  applicationUnchanged : Frozen → Bool
  nullifierLock : Bool
  nullifiers : TransferStatefulStoreCommit01.Io
  sessions : Frozen → List Nat
  commitApplication : Frozen → Store → ApplicationResult
  completeLock : Store → LockResult
  recoveryIo : Store → TransferBankRecovery.Io
  readIntent : Store → TransferBankRecovery.IntentRead
  readHistory : Store → TransferBankRecovery.HistoryRead
  capacity : Frozen → Bool

structure ParticipantResult where
  store : Store
  completed : Bool

def committed (io : Io) (store : Store) (frozen : Frozen) : TransferStoreCommitSource01.Outcome :=
  TransferStatefulStoreCommit01.commitStore io.nullifiers store frozen.insertions (io.sessions frozen)

def applied (io : Io) (store : Store) (frozen : Frozen) : ApplicationResult :=
  io.commitApplication frozen (committed io store frozen).store

def beforeCompletion (io : Io) (store : Store) (frozen : Frozen) : Store :=
  observe (committed io store frozen).store (applied io store frozen).physical

def locked (io : Io) (store : Store) (frozen : Frozen) : LockResult :=
  io.completeLock (beforeCompletion io store frozen)

def recoveryInput (io : Io) (store : Store) (frozen : Frozen) : Store :=
  observe (beforeCompletion io store frozen) (locked io store frozen).physical

def recovered (io : Io) (store : Store) (frozen : Frozen) : TransferBankRecovery.Outcome :=
  let current := recoveryInput io store frozen
  TransferBankRecovery.recover current (io.recoveryIo current) frozen.next.nullifiers
    (io.readIntent current) (io.readHistory current)

def participants (io : Io) (store : Store) (frozen : Frozen) : ParticipantResult :=
  if io.applicationUnchanged frozen = true then
    if io.nullifierLock = true then
      if (committed io store frozen).returned.isSome = true then
        match (applied io store frozen).root with
        | none => ⟨beforeCompletion io store frozen, false⟩
        | some root => if some root = frozen.next.applicationRoot then
            if (locked io store frozen).acquired = true then
              ⟨(recovered io store frozen).store, decide ((recovered io store frozen).error = none)⟩
            else ⟨recoveryInput io store frozen, false⟩
          else ⟨beforeCompletion io store frozen, false⟩
      else ⟨(committed io store frozen).store, false⟩
    else ⟨store, false⟩
  else ⟨store, false⟩

structure WriterResult where
  phase : Phase
  returned : Option CommitBoundary
  store : Store

def commitWriter (io : Io) (store : Store) (phase : Phase) : WriterResult :=
  match phase with
  | .sealed frozen =>
    let result := participants io store frozen
    if result.completed = true then
      ⟨.ready frozen.next, if io.capacity frozen = true then some frozen.next else none, result.store⟩
    else ⟨.interrupted, none, result.store⟩
  | _ => ⟨phase, none, store⟩

theorem whole_participant_success_derives_actual_temporal_inputs_and_recovery
    (io : Io) (store : Store) (frozen : Frozen)
    (success : (participants io store frozen).completed = true) :
    io.applicationUnchanged frozen = true ∧ io.nullifierLock = true ∧
      (committed io store frozen).returned.isSome = true ∧ ∃ root,
      (applied io store frozen).root = some root ∧ some root = frozen.next.applicationRoot ∧
      (locked io store frozen).acquired = true ∧
      (recovered io store frozen).error = none ∧
      (participants io store frozen).store = (recovered io store frozen).store ∧
      (recovered io store frozen).store.ready = true ∧
      (recovered io store frozen).store.actualRoots = frozen.next.nullifiers.roots ∧
      (recovered io store frozen).store.boundary = some frozen.next.nullifiers ∧
      frozen.next.nullifiers.roots.length = 16 ∧
      TransferBankRecovery.HistoryValid frozen.next.nullifiers (io.readHistory (recoveryInput io store frozen)) ∧
      (recovered io store frozen).store.healthy = (io.recoveryIo (recoveryInput io store frozen)).healthyAfter := by
  unfold participants at success
  split at success
  next version =>
    split at success
    next nullifierLock =>
      split at success
      next nullifiers =>
        cases application : (applied io store frozen).root with
        | none => simp only [application] at success; cases success
        | some root =>
          simp only [application] at success
          split at success
          next rootMatch =>
            split at success
            next completionLock =>
              have clean : (recovered io store frozen).error = none := of_decide_eq_true success
              have complete := TransferBankRecovery.recovery_success_boundary
                (recoveryInput io store frozen) (io.recoveryIo (recoveryInput io store frozen))
                frozen.next.nullifiers (io.readIntent (recoveryInput io store frozen))
                (io.readHistory (recoveryInput io store frozen)) (recovered io store frozen) rfl clean
              have same : (participants io store frozen).store = (recovered io store frozen).store := by
                simp only [participants, if_pos version, if_pos nullifierLock, if_pos nullifiers,
                  application, if_pos rootMatch, if_pos completionLock]
              exact ⟨version, nullifierLock, nullifiers, root, rfl, rootMatch, completionLock,
                clean, same, complete⟩
            next refused => cases success
          next refused => cases success
      next refused => cases success
    next refused => cases success
  next refused => cases success

theorem failed_nullifier_commit_retains_progress_and_suppresses_application_and_recovery
    (io : Io) (store : Store) (frozen : Frozen)
    (version : io.applicationUnchanged frozen = true) (nullifierLock : io.nullifierLock = true)
    (failed : (committed io store frozen).returned.isSome = false) :
    participants io store frozen = ⟨(committed io store frozen).store, false⟩ := by
  simp only [participants, if_pos version, if_pos nullifierLock, failed, Bool.false_eq_true, if_false]

theorem actual_application_root_mismatch_retains_application_observation_and_suppresses_recovery
    (io : Io) (store : Store) (frozen : Frozen) (root : Nat)
    (version : io.applicationUnchanged frozen = true) (nullifierLock : io.nullifierLock = true)
    (nullifiers : (committed io store frozen).returned.isSome = true)
    (application : (applied io store frozen).root = some root)
    (mismatch : some root ≠ frozen.next.applicationRoot) :
    participants io store frozen = ⟨beforeCompletion io store frozen, false⟩ := by
  simp only [participants, if_pos version, if_pos nullifierLock, if_pos nullifiers, application, if_neg mismatch]

theorem capacity_failure_keeps_ready_owner_and_exact_completed_physical_store
    (io : Io) (store : Store) (frozen : Frozen)
    (completed : (participants io store frozen).completed = true) (capacity : io.capacity frozen = false) :
    (commitWriter io store (.sealed frozen)).phase = .ready frozen.next ∧
      (commitWriter io store (.sealed frozen)).returned = none ∧
      (commitWriter io store (.sealed frozen)).store = (recovered io store frozen).store := by
  obtain ⟨_, _, _, _, _, _, _, _, same, _⟩ :=
    whole_participant_success_derives_actual_temporal_inputs_and_recovery io store frozen completed
  exact ⟨by simp only [commitWriter, if_pos completed],
    by simp only [commitWriter, if_pos completed, capacity, Bool.false_eq_true, if_false],
    by simpa only [commitWriter, if_pos completed] using same⟩

set_option pp.all true in
#check @ApplicationResult
#print axioms ApplicationResult
set_option pp.all true in
#check @LockResult
#print axioms LockResult
set_option pp.all true in
#check @Io
#print axioms Io
set_option pp.all true in
#check @ParticipantResult
#print axioms ParticipantResult
set_option pp.all true in
#check @committed
#print axioms committed
set_option pp.all true in
#check @applied
#print axioms applied
set_option pp.all true in
#check @beforeCompletion
#print axioms beforeCompletion
set_option pp.all true in
#check @locked
#print axioms locked
set_option pp.all true in
#check @recoveryInput
#print axioms recoveryInput
set_option pp.all true in
#check @recovered
#print axioms recovered
set_option pp.all true in
#check @participants
#print axioms participants
set_option pp.all true in
#check @WriterResult
#print axioms WriterResult
set_option pp.all true in
#check @commitWriter
#print axioms commitWriter
set_option pp.all true in
#check @whole_participant_success_derives_actual_temporal_inputs_and_recovery
#print axioms whole_participant_success_derives_actual_temporal_inputs_and_recovery
set_option pp.all true in
#check @failed_nullifier_commit_retains_progress_and_suppresses_application_and_recovery
#print axioms failed_nullifier_commit_retains_progress_and_suppresses_application_and_recovery
set_option pp.all true in
#check @actual_application_root_mismatch_retains_application_observation_and_suppresses_recovery
#print axioms actual_application_root_mismatch_retains_application_observation_and_suppresses_recovery
set_option pp.all true in
#check @capacity_failure_keeps_ready_owner_and_exact_completed_physical_store
#print axioms capacity_failure_keeps_ready_owner_and_exact_completed_physical_store
end ShielddSecurity.TransferStatefulParticipantRecovery01
