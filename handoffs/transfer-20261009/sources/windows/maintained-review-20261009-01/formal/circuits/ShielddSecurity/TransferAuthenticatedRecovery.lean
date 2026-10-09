import ShielddSecurity.TransferBoundarySourceBridge
import ShielddSecurity.TransferBankRecovery

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferAuthenticatedRecovery

open TransferReadback TransferBoundarySourceBridge TransferBankRecovery

/-! Independent composition matching PermanentWriter's authenticated snapshot
read followed by Store recovery. It cannot choose an intent boundary instead.
Native source refinement, codecs, snapshot consistency and upstream membership
contracts remain visible; a successful model trace is not a runtime receipt. -/

def run (verify : Verifier) (decode : Bytes → Option Boundary)
    (rootsHash : List Nat → Bytes) (snapshot : TransferBoundarySourceBridge.Snapshot)
    (expectedRoot : Nat) (store : Store) (io : Io) (intent : IntentRead)
    (history : HistoryRead) : Option (Boundary × Outcome) :=
  match readCommitted verify decode rootsHash snapshot expectedRoot with
  | none => none
  | some boundary => some (boundary, recover store io boundary intent history)

theorem selected_target (verify decode rootsHash snapshot expectedRoot store io intent history boundary result)
    (success : run verify decode rootsHash snapshot expectedRoot store io intent history =
      some (boundary, result)) :
    readCommitted verify decode rootsHash snapshot expectedRoot = some boundary ∧
      recover store io boundary intent history = result := by
  cases selected : readCommitted verify decode rootsHash snapshot expectedRoot with
  | none => simp only [run, selected] at success; cases success
  | some target =>
      have same : (target, recover store io target intent history) = (boundary, result) :=
        Option.some.inj (by simpa only [run, selected] using success)
      have targetSame : target = boundary := congrArg Prod.fst same
      subst target
      exact ⟨rfl, congrArg Prod.snd same⟩

theorem authenticated_recovery_consequence
    (verify decode rootsHash snapshot expectedRoot store io intent history boundary result leaves)
    (membership : MembershipContract verify leaves)
    (consistent : SnapshotConsistent snapshot)
    (success : run verify decode rootsHash snapshot expectedRoot store io intent history =
      some (boundary, result))
    (clean : result.error = none) :
    leaves expectedRoot boundaryKey = snapshot.raw boundaryKey ∧
      leaves expectedRoot rootKey = some (rootsHash boundary.roots) ∧
      leaves expectedRoot formatKey = some formatBytes ∧
      boundary.height = some snapshot.height ∧
      result.store.ready = true ∧ result.store.actualRoots = boundary.roots ∧
      result.store.boundary = some boundary ∧ boundary.roots.length = 16 ∧
      HistoryValid boundary history ∧ result.store.healthy = io.healthyAfter := by
  have selected := selected_target _ _ _ _ _ _ _ _ _ _ _ success
  have source := committed_three_key_membership _ _ _ _ _ _ _ membership consistent selected.1
  have recovered := recovery_success_boundary _ _ _ _ _ _ selected.2 clean
  exact ⟨source.1, source.2.1, source.2.2.1, source.2.2.2,
    recovered.1, recovered.2.1, recovered.2.2.1, recovered.2.2.2.1,
    recovered.2.2.2.2.1, recovered.2.2.2.2.2⟩

theorem recovered_reader_gate
    (verify decode rootsHash snapshot expectedRoot store io intent history boundary result path)
    (success : run verify decode rootsHash snapshot expectedRoot store io intent history =
      some (boundary, result))
    (clean : result.error = none) (healthy : io.healthyAfter = true)
    (width : path.length = 32) (byte : path.getD 0 0 < 256) :
    ReadGate result.store boundary path := by
  have selected := selected_target _ _ _ _ _ _ _ _ _ _ _ success
  exact ready_recovery_read_gate _ _ _ _ _ _ _ selected.2 clean healthy width byte

theorem wrong_root_cannot_recover (verify decode rootsHash snapshot expectedRoot store io intent history)
    (wrong : snapshot.root ≠ expectedRoot) :
    run verify decode rootsHash snapshot expectedRoot store io intent history = none := by
  simp only [run, wrong_application_root_refused _ _ _ _ _ wrong]

set_option pp.all true in
#check @selected_target
#print axioms selected_target
set_option pp.all true in
#check @authenticated_recovery_consequence
#print axioms authenticated_recovery_consequence
set_option pp.all true in
#check @recovered_reader_gate
#print axioms recovered_reader_gate
set_option pp.all true in
#check @wrong_root_cannot_recover
#print axioms wrong_root_cannot_recover

end ShielddSecurity.TransferAuthenticatedRecovery
