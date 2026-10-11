import ShielddSecurity.TransferPersistIntentSource01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferStoreCommitSource01
open TransferStateDelta (Bytes)
open TransferReadback (Store Boundary)
open TransferPreparedAcceptedSource01 (Prepared)
open TransferPersistIntentSource01 (Gate)

/-! Store::commit checks ready/healthy/previous boundary and roots, then reads
intent before serialization/equality. It blocks readiness before the ordered
session commits and checks actual observed roots after all returned success.
Session callbacks retain observed roots even on failure; the recurrence stops
at that failure. Native Prepared.sessions/partition indices, actual NOMT roots,
serialization/read_record, ownership, locking and durability are interfaces.
The result never makes rollback or absence of physical progress an error fact.
Returning a transition leaves ready false; Store::complete is a later operation.
No native/control/full Transfer certification is supplied here. -/

structure SessionResult where
  roots : List Nat
  succeeded : Bool

structure Io where
  readIntent : Option Bytes
  serialize : Prepared → Option Bytes
  commitSession : Nat → List Nat → SessionResult

def walkSessions (commit : Nat → List Nat → SessionResult) (roots : List Nat) : List Nat → SessionResult
  | [] => ⟨roots, true⟩
  | index :: rest =>
    let observed := commit index roots
    if observed.succeeded = true then walkSessions commit observed.roots rest
    else ⟨observed.roots, false⟩

def AllCommitted (commit : Nat → List Nat → SessionResult) (roots : List Nat) : List Nat → List Nat → Prop
  | [], final => final = roots
  | index :: rest, final =>
    (commit index roots).succeeded = true ∧ AllCommitted commit (commit index roots).roots rest final

structure Outcome where
  store : Store
  returned : Option Prepared

def finishParticipants (store : Store) (prepared : Prepared) (observed : SessionResult) : Outcome :=
  ⟨{store with ready := false, actualRoots := observed.roots},
    if observed.succeeded = true ∧ observed.roots = prepared.next.roots then some prepared else none⟩

def commitStore (io : Io) (store : Store) (prepared : Prepared) (sessions : List Nat) : Outcome := by
  letI : Decidable (Gate store prepared) := by unfold Gate; infer_instance
  exact if Gate store prepared then
    match io.readIntent with
    | none => ⟨store, none⟩
    | some record => match io.serialize prepared with
      | none => ⟨store, none⟩
      | some bytes => if record = bytes then
          finishParticipants store prepared (walkSessions io.commitSession store.actualRoots sessions)
        else ⟨store, none⟩
  else ⟨store, none⟩

theorem successful_session_walk_derives_each_observed_commit
    (commit : Nat → List Nat → SessionResult) (roots : List Nat) (sessions : List Nat)
    (success : (walkSessions commit roots sessions).succeeded = true) :
    AllCommitted commit roots sessions (walkSessions commit roots sessions).roots := by
  induction sessions generalizing roots with
  | nil => rfl
  | cons index rest ih =>
    simp only [walkSessions] at success
    split at success
    next committed =>
      change (commit index roots).succeeded = true ∧
        AllCommitted commit (commit index roots).roots rest (walkSessions commit roots (index :: rest)).roots
      rw [walkSessions, if_pos committed]
      exact ⟨committed, ih _ success⟩
    next refused => cases success

theorem failed_session_head_retains_observed_roots_and_suppresses_suffix
    (commit : Nat → List Nat → SessionResult) (roots : List Nat) (index : Nat) (rest : List Nat)
    (failed : (commit index roots).succeeded = false) :
    walkSessions commit roots (index :: rest) = ⟨(commit index roots).roots, false⟩ := by
  simp only [walkSessions, failed, Bool.false_eq_true, if_false]

theorem participant_finish_keeps_readiness_blocked_and_exact_observed_roots
    (store : Store) (prepared : Prepared) (observed : SessionResult)
    (hash : String → Nat → List Nat) (verify : Nat → List Nat → Nat → Bool → Bool)
    (requested : Boundary) (nullifier : Nat) (candidate : Option (Bool × Nat)) :
    (finishParticipants store prepared observed).store.ready = false ∧
      (finishParticipants store prepared observed).store.actualRoots = observed.roots ∧
      (finishParticipants store prepared observed).store.boundary = store.boundary ∧
      TransferReadback.status hash verify (finishParticipants store prepared observed).store requested nullifier candidate = none := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact TransferReadback.interrupted_status_unavailable hash verify {store with actualRoots := observed.roots} requested nullifier candidate

theorem returned_transition_derives_all_participant_success_and_root_match
    (store : Store) (prepared : Prepared) (observed : SessionResult) (returned : Prepared)
    (success : (finishParticipants store prepared observed).returned = some returned) :
    observed.succeeded = true ∧ observed.roots = prepared.next.roots ∧ returned = prepared := by
  change (if observed.succeeded = true ∧ observed.roots = prepared.next.roots then some prepared else none) = some returned at success
  split at success
  next checked => exact ⟨checked.1, checked.2, (Option.some.inj success).symm⟩
  next refused => cases success

theorem whole_store_commit_success_derives_intent_calls_ordered_session_success_and_observed_next_roots
    (io : Io) (store : Store) (prepared : Prepared) (sessions : List Nat) (returned : Prepared)
    (success : (commitStore io store prepared sessions).returned = some returned) :
    Gate store prepared ∧ ∃ record bytes,
      io.readIntent = some record ∧ io.serialize prepared = some bytes ∧ record = bytes ∧
      (walkSessions io.commitSession store.actualRoots sessions).succeeded = true ∧
      AllCommitted io.commitSession store.actualRoots sessions (walkSessions io.commitSession store.actualRoots sessions).roots ∧
      (walkSessions io.commitSession store.actualRoots sessions).roots = prepared.next.roots ∧
      returned = prepared ∧
      (commitStore io store prepared sessions).store =
        {store with ready := false, actualRoots := (walkSessions io.commitSession store.actualRoots sessions).roots} := by
  unfold commitStore at success
  split at success
  next gate =>
    cases read : io.readIntent with
    | none => simp only [read] at success
    | some record =>
      cases serialized : io.serialize prepared with
      | none => simp only [read, serialized] at success
      | some bytes =>
        by_cases equal : record = bytes
        · have completed : (finishParticipants store prepared (walkSessions io.commitSession store.actualRoots sessions)).returned = some returned := by
            simpa only [read, serialized, if_pos equal] using success
          have checked := returned_transition_derives_all_participant_success_and_root_match store prepared _ returned completed
          refine ⟨gate, record, bytes, read, serialized, equal, checked.1,
            successful_session_walk_derives_each_observed_commit _ _ _ checked.1, checked.2.1, checked.2.2, ?_⟩
          simp only [commitStore, if_pos gate, read, serialized, if_pos equal, finishParticipants]
        · simp only [read, serialized, if_neg equal] at success
  next refused => cases success

theorem unavailable_intent_refuses_before_sessions_with_original_store
    (io : Io) (store : Store) (prepared : Prepared) (sessions : List Nat)
    (unavailable : io.readIntent = none) :
    commitStore io store prepared sessions = ⟨store, none⟩ := by
  unfold commitStore
  split
  · rw [unavailable]
  · rfl

set_option pp.all true in
#check @SessionResult
#print axioms SessionResult
set_option pp.all true in
#check @Io
#print axioms Io
set_option pp.all true in
#check @walkSessions
#print axioms walkSessions
set_option pp.all true in
#check @AllCommitted
#print axioms AllCommitted
set_option pp.all true in
#check @Outcome
#print axioms Outcome
set_option pp.all true in
#check @finishParticipants
#print axioms finishParticipants
set_option pp.all true in
#check @commitStore
#print axioms commitStore
set_option pp.all true in
#check @successful_session_walk_derives_each_observed_commit
#print axioms successful_session_walk_derives_each_observed_commit
set_option pp.all true in
#check @failed_session_head_retains_observed_roots_and_suppresses_suffix
#print axioms failed_session_head_retains_observed_roots_and_suppresses_suffix
set_option pp.all true in
#check @participant_finish_keeps_readiness_blocked_and_exact_observed_roots
#print axioms participant_finish_keeps_readiness_blocked_and_exact_observed_roots
set_option pp.all true in
#check @returned_transition_derives_all_participant_success_and_root_match
#print axioms returned_transition_derives_all_participant_success_and_root_match
set_option pp.all true in
#check @whole_store_commit_success_derives_intent_calls_ordered_session_success_and_observed_next_roots
#print axioms whole_store_commit_success_derives_intent_calls_ordered_session_success_and_observed_next_roots
set_option pp.all true in
#check @unavailable_intent_refuses_before_sessions_with_original_store
#print axioms unavailable_intent_refuses_before_sessions_with_original_store
end ShielddSecurity.TransferStoreCommitSource01
