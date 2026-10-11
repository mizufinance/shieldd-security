import ShielddSecurity.TransferRecordReadBound01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferStatefulStoreCommit01
open TransferStateDelta (Bytes)
open TransferReadback (Store Boundary interrupt)
open TransferPreparedAcceptedSource01 (Prepared)
open TransferPersistIntentSource01 (Gate)

/-! Source Store::commit with physical roots and current poison-health ghosts
threaded across each actual session result and the final actual_roots read.
Ghost observations add no native call or desired-state premise. Only roots and
health come from observations; ready and boundary are owned Store fields.
Every failure retains observed physical progress. Returned success requires
the final independently observed roots to match the proposed next roots.
Native NOMT/lock/ownership/session/index/serde/OS and ghost-observation
correspondence remain interfaces; no success implies healthy or durability.
The old snapshot-health model is not claimed to prove current health. -/

structure Physical where
  roots : List Nat
  healthy : Bool

def observe (store : Store) (physical : Physical) : Store :=
  {store with actualRoots := physical.roots, healthy := physical.healthy}

structure SessionResult where
  physical : Physical
  succeeded : Bool

structure Io where
  readIntent : Option Bytes
  serialize : Prepared → Option Bytes
  commitSession : Nat → Store → SessionResult
  actualAfterSessions : Store → Physical

structure WalkResult where
  store : Store
  succeeded : Bool

def walkSessions (commit : Nat → Store → SessionResult) (store : Store) : List Nat → WalkResult
  | [] => ⟨store, true⟩
  | index :: rest =>
    let result := commit index store
    let current := observe store result.physical
    if result.succeeded = true then walkSessions commit current rest else ⟨current, false⟩

def AllCommitted (commit : Nat → Store → SessionResult) (store : Store) : List Nat → Store → Prop
  | [], final => final = store
  | index :: rest, final =>
    (commit index store).succeeded = true ∧
      AllCommitted commit (observe store (commit index store).physical) rest final

def commitStore (io : Io) (store : Store) (prepared : Prepared) (sessions : List Nat) : TransferStoreCommitSource01.Outcome := by
  letI : Decidable (Gate store prepared) := by unfold Gate; infer_instance
  exact if Gate store prepared then
    match io.readIntent with
    | none => ⟨store, none⟩
    | some record => match io.serialize prepared with
      | none => ⟨store, none⟩
      | some bytes => if record = bytes then
          let walked := walkSessions io.commitSession (interrupt store) sessions
          if walked.succeeded = true then
            let current := observe walked.store (io.actualAfterSessions walked.store)
            ⟨current, if current.actualRoots = prepared.next.roots then some prepared else none⟩
          else ⟨walked.store, none⟩
        else ⟨store, none⟩
  else ⟨store, none⟩

theorem session_walk_frames_ready_and_boundary (commit : Nat → Store → SessionResult) (store : Store) (sessions : List Nat) :
    (walkSessions commit store sessions).store.ready = store.ready ∧
      (walkSessions commit store sessions).store.boundary = store.boundary := by
  induction sessions generalizing store with
  | nil => exact ⟨rfl, rfl⟩
  | cons index rest ih =>
    by_cases succeeded : (commit index store).succeeded = true
    · simp only [walkSessions, if_pos succeeded]
      exact ih _
    · simp only [walkSessions, if_neg succeeded]
      exact ⟨rfl, rfl⟩

theorem successful_session_walk_derives_state_threaded_actual_calls
    (commit : Nat → Store → SessionResult) (store : Store) (sessions : List Nat)
    (success : (walkSessions commit store sessions).succeeded = true) :
    AllCommitted commit store sessions (walkSessions commit store sessions).store := by
  induction sessions generalizing store with
  | nil => rfl
  | cons index rest ih =>
    simp only [walkSessions] at success
    split at success
    next succeeded =>
      change (commit index store).succeeded = true ∧
        AllCommitted commit (observe store (commit index store).physical) rest
          (walkSessions commit store (index :: rest)).store
      rw [walkSessions, if_pos succeeded]
      exact ⟨succeeded, ih _ success⟩
    next failed => cases success

theorem failed_session_keeps_actual_roots_and_current_poison_health
    (commit : Nat → Store → SessionResult) (store : Store) (index : Nat) (rest : List Nat)
    (failed : (commit index store).succeeded = false) :
    walkSessions commit store (index :: rest) = ⟨observe store (commit index store).physical, false⟩ ∧
      (walkSessions commit store (index :: rest)).store.actualRoots = (commit index store).physical.roots ∧
      (walkSessions commit store (index :: rest)).store.healthy = (commit index store).physical.healthy := by
  have exactResult : walkSessions commit store (index :: rest) = ⟨observe store (commit index store).physical, false⟩ := by
    simp only [walkSessions, failed, Bool.false_eq_true, if_false]
  exact ⟨exactResult, by rw [exactResult]; rfl, by rw [exactResult]; rfl⟩

theorem whole_success_derives_actual_read_serialization_sessions_and_final_observation
    (io : Io) (store : Store) (prepared : Prepared) (sessions : List Nat) (returned : Prepared)
    (success : (commitStore io store prepared sessions).returned = some returned) :
    Gate store prepared ∧ ∃ record bytes,
      io.readIntent = some record ∧ io.serialize prepared = some bytes ∧ record = bytes ∧
      (walkSessions io.commitSession (interrupt store) sessions).succeeded = true ∧
      AllCommitted io.commitSession (interrupt store) sessions (walkSessions io.commitSession (interrupt store) sessions).store ∧
      (io.actualAfterSessions (walkSessions io.commitSession (interrupt store) sessions).store).roots = prepared.next.roots ∧
      returned = prepared ∧
      (commitStore io store prepared sessions).store = observe
        (walkSessions io.commitSession (interrupt store) sessions).store
        (io.actualAfterSessions (walkSessions io.commitSession (interrupt store) sessions).store) := by
  unfold commitStore at success
  split at success
  next gate =>
    cases read : io.readIntent with
    | none => simp only [read] at success; cases success
    | some record =>
      cases serialized : io.serialize prepared with
      | none => simp only [read, serialized] at success; cases success
      | some bytes =>
        by_cases equal : record = bytes
        · simp only [read, serialized, if_pos equal] at success
          split at success
          next walked =>
            split at success
            next roots =>
              have finalStore : (commitStore io store prepared sessions).store = observe
                  (walkSessions io.commitSession (interrupt store) sessions).store
                  (io.actualAfterSessions (walkSessions io.commitSession (interrupt store) sessions).store) := by
                simp only [commitStore, if_pos gate, read, serialized, if_pos equal, if_pos walked]
              exact ⟨gate, record, bytes, rfl, rfl, equal, walked,
                successful_session_walk_derives_state_threaded_actual_calls _ _ _ walked,
                roots, (Option.some.inj success).symm, finalStore⟩
            next refused => cases success
          next refused => cases success
        · simp only [read, serialized, if_neg equal] at success; cases success
  next refused => cases success

theorem returned_commit_keeps_reads_blocked_and_independently_observed_health
    (io : Io) (store : Store) (prepared : Prepared) (sessions : List Nat) (returned : Prepared)
    (success : (commitStore io store prepared sessions).returned = some returned)
    (hash : String → Nat → List Nat) (verify : Nat → List Nat → Nat → Bool → Bool)
    (requested : Boundary) (nullifier : Nat) (candidate : Option (Bool × Nat)) :
    (commitStore io store prepared sessions).store.ready = false ∧
      (commitStore io store prepared sessions).store.boundary = store.boundary ∧
      (commitStore io store prepared sessions).store.healthy =
        (io.actualAfterSessions (walkSessions io.commitSession (interrupt store) sessions).store).healthy ∧
      TransferReadback.status hash verify (commitStore io store prepared sessions).store requested nullifier candidate = none := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, finalStore⟩ :=
    whole_success_derives_actual_read_serialization_sessions_and_final_observation io store prepared sessions returned success
  have frames := session_walk_frames_ready_and_boundary io.commitSession (interrupt store) sessions
  have blocked : (commitStore io store prepared sessions).store.ready = false := by rw [finalStore]; exact frames.1
  have boundary : (commitStore io store prepared sessions).store.boundary = store.boundary := by rw [finalStore]; exact frames.2
  have statusNone : TransferReadback.status hash verify (commitStore io store prepared sessions).store requested nullifier candidate = none := by
    have same : interrupt (commitStore io store prepared sessions).store = (commitStore io store prepared sessions).store := by
      cases observed : (commitStore io store prepared sessions).store
      simp only [observed] at blocked
      simp only [interrupt, blocked]
    rw [← same]
    exact TransferReadback.interrupted_status_unavailable hash verify _ requested nullifier candidate
  exact ⟨blocked, boundary, by rw [finalStore]; rfl, statusNone⟩

set_option pp.all true in
#check @Physical
#print axioms Physical
set_option pp.all true in
#check @observe
#print axioms observe
set_option pp.all true in
#check @SessionResult
#print axioms SessionResult
set_option pp.all true in
#check @Io
#print axioms Io
set_option pp.all true in
#check @WalkResult
#print axioms WalkResult
set_option pp.all true in
#check @walkSessions
#print axioms walkSessions
set_option pp.all true in
#check @AllCommitted
#print axioms AllCommitted
set_option pp.all true in
#check @commitStore
#print axioms commitStore
set_option pp.all true in
#check @session_walk_frames_ready_and_boundary
#print axioms session_walk_frames_ready_and_boundary
set_option pp.all true in
#check @successful_session_walk_derives_state_threaded_actual_calls
#print axioms successful_session_walk_derives_state_threaded_actual_calls
set_option pp.all true in
#check @failed_session_keeps_actual_roots_and_current_poison_health
#print axioms failed_session_keeps_actual_roots_and_current_poison_health
set_option pp.all true in
#check @whole_success_derives_actual_read_serialization_sessions_and_final_observation
#print axioms whole_success_derives_actual_read_serialization_sessions_and_final_observation
set_option pp.all true in
#check @returned_commit_keeps_reads_blocked_and_independently_observed_health
#print axioms returned_commit_keeps_reads_blocked_and_independently_observed_health
end ShielddSecurity.TransferStatefulStoreCommit01
