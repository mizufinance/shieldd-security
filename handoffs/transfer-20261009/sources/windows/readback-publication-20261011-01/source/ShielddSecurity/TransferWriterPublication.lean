import ShielddSecurity.TransferBankRecovery

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferWriterPublication

open TransferReadback TransferBankRecovery

/-!
Independent finalization/publication program for the owned writer/Host edge.
The latest snapshot is observed after the fallible application commit; it is
not defined to equal a requested state. Earlier NOMT/application commit steps,
Bankd root authentication and native snapshot decoding remain source interfaces.
Capacity failure follows successful recovery and Ready, so an error cannot be
interpreted as absence of durable progress. Publication checks actual state.
-/

inductive Phase where
  | interrupted
  | ready (boundary : Boundary)
  deriving DecidableEq

structure Writer where
  phase : Phase
  store : Store
  latest : Snapshot
  returned : Option Unit

def complete (store : Store) (io : Io) (committed : Boundary)
    (intent : IntentRead) (history : HistoryRead) (latest : Snapshot)
    (capacity : Bool) : Writer :=
  let observed := recover store io committed intent history
  if observed.error = none then
    ⟨.ready committed, observed.store, latest, if capacity = true then some () else none⟩
  else ⟨.interrupted, observed.store, latest, none⟩

def hostIdle (writer : Writer) : Bool := writer.returned.isSome

def publishWriter (writer : Writer) (previous : Option Snapshot) (expected : ExpectedCommit) :
    Option Snapshot := publish writer.store previous writer.latest expected

theorem completed_ready (store io committed intent history latest capacity)
    (clean : (recover store io committed intent history).error = none) :
    (complete store io committed intent history latest capacity).phase = .ready committed ∧
      (complete store io committed intent history latest capacity).store =
        (recover store io committed intent history).store ∧
      (complete store io committed intent history latest capacity).latest = latest := by
  simp only [complete, if_pos clean, and_self]

theorem capacity_error_after_ready (store io committed intent history latest)
    (clean : (recover store io committed intent history).error = none) :
    (complete store io committed intent history latest false).phase = .ready committed ∧
      (complete store io committed intent history latest false).returned = none ∧
      hostIdle (complete store io committed intent history latest false) = false := by
  simp [complete, clean, hostIdle]

theorem returned_success_checks (store io committed intent history latest capacity)
    (success : (complete store io committed intent history latest capacity).returned = some ()) :
    (recover store io committed intent history).error = none ∧ capacity = true ∧
      hostIdle (complete store io committed intent history latest capacity) = true := by
  by_cases clean : (recover store io committed intent history).error = none
  · by_cases available : capacity = true
    · exact ⟨clean, available, by simp [hostIdle, success]⟩
    · simp only [complete, if_pos clean, if_neg available] at success
      cases success
  · simp only [complete, if_neg clean] at success
    cases success

theorem completed_store_boundary (store io committed intent history latest capacity)
    (clean : (recover store io committed intent history).error = none) :
    (complete store io committed intent history latest capacity).store.boundary = some committed ∧
      (complete store io committed intent history latest capacity).store.actualRoots = committed.roots ∧
      committed.roots.length = 16 := by
  have recovered := recovery_success_boundary store io committed intent history
    (recover store io committed intent history) rfl clean
  have stored := (completed_ready store io committed intent history latest capacity clean).2.1
  rw [stored]
  exact ⟨recovered.2.2.1, recovered.2.1, recovered.2.2.2.1⟩

theorem published_actual_boundary (writer previous expected response)
    (success : publishWriter writer previous expected = some response) :
    response = writer.latest ∧ writer.store.ready = true ∧ writer.store.healthy = true ∧
      writer.store.boundary = some writer.latest.boundary ∧
      writer.store.actualRoots = writer.latest.boundary.roots ∧
      writer.latest.boundary.roots.length = 16 ∧
      writer.latest.height = expected.height ∧ writer.latest.applicationRoot = expected.applicationRoot ∧
      writer.latest.boundary.height = some writer.latest.height ∧
      writer.latest.boundary.blockId = expected.blockId := by
  have checked := publication_success_exact writer.store previous writer.latest expected response success
  exact ⟨checked.1, checked.2.1, checked.2.2.1, checked.2.2.2.1,
    checked.2.2.2.2.1, checked.2.2.2.2.2.1, checked.2.2.2.2.2.2.1,
    checked.2.2.2.2.2.2.2.1, checked.2.2.2.2.2.2.2.2.1,
    checked.2.2.2.2.2.2.2.2.2.1⟩

theorem completion_publication_same_boundary
    (store io committed intent history latest capacity previous expected response)
    (clean : (recover store io committed intent history).error = none)
    (success : publishWriter (complete store io committed intent history latest capacity)
      previous expected = some response) :
    latest.boundary = committed ∧ latest.boundary.roots.length = 16 ∧
      latest.height = expected.height ∧ latest.applicationRoot = expected.applicationRoot ∧
      latest.boundary.blockId = expected.blockId := by
  have stored := (completed_store_boundary store io committed intent history latest capacity clean).1
  have published := published_actual_boundary _ _ _ _ success
  have latestSame := (completed_ready store io committed intent history latest capacity clean).2.2
  rw [latestSame] at published
  have equalBoundary : latest.boundary = committed :=
    Option.some.inj (published.2.2.2.1.symm.trans stored)
  exact ⟨equalBoundary, published.2.2.2.2.2.1, published.2.2.2.2.2.2.1,
    published.2.2.2.2.2.2.2.1, published.2.2.2.2.2.2.2.2.2⟩

theorem historical_during_interruption (hash verify store) (previous : Snapshot) (nullifier candidate) :
    status hash verify (interrupt store) previous.boundary nullifier candidate = none := by
  exact interrupted_status_unavailable _ _ _ _ _ _

theorem historical_stale_snapshot_unavailable (hash verify store) (previous : Snapshot) (nullifier candidate)
    (stale : store.boundary ≠ some previous.boundary) :
    status hash verify store previous.boundary nullifier candidate = none := by
  exact stale_boundary_unavailable _ _ _ _ _ _ stale

set_option pp.all true in
#check @completed_ready
#print axioms completed_ready
set_option pp.all true in
#check @capacity_error_after_ready
#print axioms capacity_error_after_ready
set_option pp.all true in
#check @returned_success_checks
#print axioms returned_success_checks
set_option pp.all true in
#check @completed_store_boundary
#print axioms completed_store_boundary
set_option pp.all true in
#check @published_actual_boundary
#print axioms published_actual_boundary
set_option pp.all true in
#check @completion_publication_same_boundary
#print axioms completion_publication_same_boundary
set_option pp.all true in
#check @historical_during_interruption
#print axioms historical_during_interruption
set_option pp.all true in
#check @historical_stale_snapshot_unavailable
#print axioms historical_stale_snapshot_unavailable

end ShielddSecurity.TransferWriterPublication
