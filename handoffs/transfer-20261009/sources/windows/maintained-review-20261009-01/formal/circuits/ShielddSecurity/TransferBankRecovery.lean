import ShielddSecurity.TransferReadback

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferBankRecovery

open TransferReadback

/-!
Independent recovery program for the owned permanent-nullifier store. Primitive
I/O outcomes and observed partition roots are inputs, not a completion assertion.
The program checks roots and retained history before publishing a ready boundary.
Native decoding, lock ownership, authenticated application boundary selection,
NOMT rollback and durable filesystem semantics require separate source contracts.
Failure preserves observed physical progress and keeps every read unavailable.
-/

def initial : Boundary := ⟨none, List.replicate 32 0, List.replicate 16 0⟩

structure Transition where
  previous : Boundary
  next : Boundary
  nullifiers : List Nat
  deriving DecidableEq

def TransitionValid (record : Transition) : Prop :=
  (match record.next.height with
    | none => False
    | some height => height < 2 ^ 64 ∧
        (match record.previous.height with
          | none => height = 0 ∧ record.previous = initial
          | some earlier => earlier + 1 = height)) ∧
    record.nullifiers.length ≤ 32768 ∧ record.nullifiers.Nodup ∧
    record.previous.roots.length = 16 ∧ record.next.roots.length = 16

instance (record : Transition) : Decidable (TransitionValid record) := by
  unfold TransitionValid
  cases record.next.height <;> cases record.previous.height <;> infer_instance

inductive Error where
  | intentRead | invalidIntent | boundaryConflict | unknownPartition
  | rollback | nextLagging | retain | rootMismatch | remove | sync | history
  deriving DecidableEq

inductive IntentRead where
  | missing
  | failed
  | record (value : Transition)

inductive HistoryRead where
  | unavailable
  | record (value : Transition)

def HistoryValid (committed : Boundary) (history : HistoryRead) : Prop :=
  match committed.height with
  | none => committed = initial
  | some _ => match history with
    | .unavailable => False
    | .record record => TransitionValid record ∧ record.next = committed

instance (committed : Boundary) (history : HistoryRead) :
    Decidable (HistoryValid committed history) := by
  unfold HistoryValid
  cases committed.height <;> cases history <;> infer_instance

structure Physical where
  roots : List Nat
  error : Option Error

structure Io where
  /-- Each rollback callback returns the roots observed after that native call,
  including physical progress on a failed call. No restoration is inferred. -/
  rollback : Nat → List Nat → Physical
  /-- Independently observed partition health after the recovery operations.
  Recovery success does not establish that NOMT sessions are unpoisoned. -/
  healthyAfter : Bool
  retained : Bool
  removed : Bool
  synced : Bool

def rollbacks (io : Io) (wanted : List Nat) :
    Nat → Nat → List Nat → Physical
  | _, 0, actual => ⟨actual, none⟩
  | index, remaining + 1, actual =>
      if actual.getD index 0 = wanted.getD index 0 then
        rollbacks io wanted (index + 1) remaining actual
      else
        let observed := io.rollback index actual
        match observed.error with
        | some _ => ⟨observed.roots, some .rollback⟩
        | none => rollbacks io wanted (index + 1) remaining observed.roots

def KnownPartitions (actual : List Nat) (record : Transition) : Prop :=
  actual.length = 16 ∧ ∀ index ∈ List.range 16,
    actual.getD index 0 = record.previous.roots.getD index 0 ∨
      actual.getD index 0 = record.next.roots.getD index 0

instance (actual : List Nat) (record : Transition) :
    Decidable (KnownPartitions actual record) := by
  unfold KnownPartitions
  infer_instance

def cleanIntent (io : Io) (committed : Boundary) (observed : Physical) : Physical :=
  match observed.error with
  | some _ => observed
  | none =>
      if observed.roots ≠ committed.roots then ⟨observed.roots, some .rootMismatch⟩
      else if io.removed = false then ⟨observed.roots, some .remove⟩
      else if io.synced = false then ⟨observed.roots, some .sync⟩
      else observed

def prepare (io : Io) (actual : List Nat) (committed : Boundary)
    (intent : IntentRead) : Physical :=
  match intent with
  | .failed => ⟨actual, some .intentRead⟩
  | .missing =>
      if actual = committed.roots then ⟨actual, none⟩
      else ⟨actual, some .rootMismatch⟩
  | .record record =>
      if ¬ TransitionValid record then ⟨actual, some .invalidIntent⟩
      else if ¬ (committed = record.previous ∨ committed = record.next) then
        ⟨actual, some .boundaryConflict⟩
      else if ¬ KnownPartitions actual record then ⟨actual, some .unknownPartition⟩
      else if committed = record.previous then
        cleanIntent io committed (rollbacks io committed.roots 0 16 actual)
      else if actual ≠ committed.roots then ⟨actual, some .nextLagging⟩
      else if io.retained = false then ⟨actual, some .retain⟩
      else cleanIntent io committed ⟨actual, none⟩

structure Outcome where
  store : Store
  error : Option Error

def unavailable (store : Store) (roots : List Nat) (error : Error) : Outcome :=
  ⟨{ store with ready := false, actualRoots := roots }, some error⟩

def FinalGate (roots : List Nat) (committed : Boundary) (history : HistoryRead) : Prop :=
  roots = committed.roots ∧ committed.roots.length = 16 ∧ HistoryValid committed history

instance (roots : List Nat) (committed : Boundary) (history : HistoryRead) :
    Decidable (FinalGate roots committed history) := by
  unfold FinalGate
  infer_instance

def finish (store : Store) (roots : List Nat) (committed : Boundary)
    (history : HistoryRead) : Outcome :=
  if FinalGate roots committed history then
    ⟨{ store with ready := true, actualRoots := roots, boundary := some committed }, none⟩
  else unavailable store roots .history

def recover (store : Store) (io : Io) (committed : Boundary)
    (intent : IntentRead) (history : HistoryRead) : Outcome :=
  let observed := prepare io store.actualRoots committed intent
  match observed.error with
  | some error => unavailable { store with healthy := io.healthyAfter } observed.roots error
  | none => finish { store with healthy := io.healthyAfter } observed.roots committed history

theorem rollback_failure_retains_observed_roots (io wanted index remaining actual error)
    (changed : actual.getD index 0 ≠ wanted.getD index 0)
    (failed : (io.rollback index actual).error = some error) :
    rollbacks io wanted index (remaining + 1) actual =
      ⟨(io.rollback index actual).roots, some .rollback⟩ := by
  simp only [rollbacks, if_neg changed, failed]

theorem finish_success (store roots committed history) (result : Outcome)
    (success : finish store roots committed history = result)
    (clean : result.error = none) :
    FinalGate roots committed history ∧ result.store.ready = true ∧
      result.store.actualRoots = committed.roots ∧ result.store.boundary = some committed ∧
      result.store.healthy = store.healthy := by
  by_cases gate : FinalGate roots committed history
  · have same :
        (⟨{ store with ready := true, actualRoots := roots, boundary := some committed }, none⟩ : Outcome) =
          result := by
      simpa only [finish, if_pos gate] using success
    rw [← same]
    exact ⟨gate, rfl, gate.1, rfl, rfl⟩
  · have failed : result.error = some Error.history := by
      rw [← success]
      simp only [finish, if_neg gate, unavailable]
    rw [failed] at clean
    cases clean

theorem recovery_success_boundary (store io committed intent history) (result : Outcome)
    (success : recover store io committed intent history = result)
    (clean : result.error = none) :
    result.store.ready = true ∧ result.store.actualRoots = committed.roots ∧
      result.store.boundary = some committed ∧ committed.roots.length = 16 ∧
      HistoryValid committed history ∧ result.store.healthy = io.healthyAfter := by
  cases observed : (prepare io store.actualRoots committed intent).error with
  | none =>
      have completed : finish { store with healthy := io.healthyAfter }
          (prepare io store.actualRoots committed intent).roots
          committed history = result := by
        simpa only [recover, observed] using success
      have checks := finish_success _ _ _ _ result completed clean
      exact ⟨checks.2.1, checks.2.2.1, checks.2.2.2.1,
        checks.1.2.1, checks.1.2.2, checks.2.2.2.2⟩
  | some error =>
      have failed : result.error = some error := by
        rw [← success]
        simp only [recover, observed, unavailable]
      rw [failed] at clean
      cases clean

theorem failed_finish_unavailable (hash verify store roots committed history requested nullifier candidate)
    (blocked : ¬ FinalGate roots committed history) :
    status hash verify (finish store roots committed history).store requested nullifier candidate = none := by
  simp [finish, blocked, unavailable, status, ReadGate]

theorem physical_failure_unavailable (hash verify store io committed intent history requested nullifier candidate)
    (error : Error) (failed : (prepare io store.actualRoots committed intent).error = some error) :
    status hash verify (recover store io committed intent history).store requested nullifier candidate = none := by
  simp [recover, failed, unavailable, status, ReadGate]

theorem missing_intent_root_mismatch (io actual committed)
    (wrong : actual ≠ committed.roots) :
    prepare io actual committed .missing = ⟨actual, some .rootMismatch⟩ := by
  simp only [prepare, if_neg wrong]

theorem unknown_application_boundary_refused (io actual committed record)
    (valid : TransitionValid record)
    (wrong : ¬ (committed = record.previous ∨ committed = record.next)) :
    prepare io actual committed (.record record) = ⟨actual, some .boundaryConflict⟩ := by
  simp [prepare, valid, wrong]

theorem next_lagging_refused (io actual record)
    (valid : TransitionValid record) (known : KnownPartitions actual record)
    (distinct : record.next ≠ record.previous) (lagging : actual ≠ record.next.roots) :
    prepare io actual record.next (.record record) = ⟨actual, some .nextLagging⟩ := by
  simp [prepare, valid, known, distinct, lagging]

theorem valid_initial_history (committed history)
    (empty : committed.height = none) (valid : HistoryValid committed history) :
    committed = initial := by
  simpa only [HistoryValid, empty] using valid

theorem ready_recovery_read_gate (store io committed intent history result path)
    (success : recover store io committed intent history = result)
    (clean : result.error = none) (healthy : io.healthyAfter = true)
    (width : path.length = 32) (byte : path.getD 0 0 < 256) :
    ReadGate result.store committed path := by
  have checks := recovery_success_boundary _ _ _ _ _ result success clean
  exact ⟨checks.1, checks.2.2.2.2.2.trans healthy, checks.2.1,
    checks.2.2.1, checks.2.2.2.1, width, byte⟩

set_option pp.all true in
#check @rollback_failure_retains_observed_roots
#print axioms rollback_failure_retains_observed_roots
set_option pp.all true in
#check @finish_success
#print axioms finish_success
set_option pp.all true in
#check @recovery_success_boundary
#print axioms recovery_success_boundary
set_option pp.all true in
#check @failed_finish_unavailable
#print axioms failed_finish_unavailable
set_option pp.all true in
#check @physical_failure_unavailable
#print axioms physical_failure_unavailable
set_option pp.all true in
#check @missing_intent_root_mismatch
#print axioms missing_intent_root_mismatch
set_option pp.all true in
#check @unknown_application_boundary_refused
#print axioms unknown_application_boundary_refused
set_option pp.all true in
#check @next_lagging_refused
#print axioms next_lagging_refused
set_option pp.all true in
#check @valid_initial_history
#print axioms valid_initial_history
set_option pp.all true in
#check @ready_recovery_read_gate
#print axioms ready_recovery_read_gate

end ShielddSecurity.TransferBankRecovery
