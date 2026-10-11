import ShielddSecurity.TransferHostSeal01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferWriterRecoverCurrent01
open TransferStateDelta (Bytes State)
open TransferReadback (Store)
open TransferWriterPrepareSource01 (Phase CommitBoundary)

/-! Source recover_current drops disposable writer sessions by replacing the
phase with Interrupted before observing latest_snapshot. A u64::MAX version
selects the actual default boundary; otherwise the actual returned root and
read_committed_boundary select the recovery boundary. Actual database lock
observation is the exact Store input to captured-initial recovery; no desired
recovery Store is supplied. Only returned clean recovery sets Ready.
recover_current checks the snapshot's own root; external Host commitment
validation belongs to the distinct recover/open/publication path. Snapshot
immutability/getRaw/proof coherence and ICS23 verifier soundness are separate
contracts. Native ghosts/partition frames/current root and poison observations,
finite root/version/height/serde/library/lock/ownership/OS correspondence remain
interfaces. No healthy/durable/externally-authenticated conclusion inferred. -/

structure Snapshot (O : Type) where
  version : Fin (2 ^ 64)
  state : State O
  root : Option Nat
  authentication : TransferAuthenticatedBoundarySource01.Io O
  reader : TransferBoundaryReaderSource01.Io O
  project : Bytes → Nat

structure LockResult where
  store : Store
  acquired : Bool

structure Io (O : Type) where
  snapshot : Snapshot O
  lock : Store → LockResult
  recoveryIo : Store → TransferBankRecovery.Io
  readIntent : Store → TransferBankRecovery.IntentRead
  readHistory : Store → TransferBankRecovery.HistoryRead

structure Outcome where
  phase : Phase
  store : Store
  succeeded : Bool

def selected {O : Type} (snapshot : Snapshot O) : Option CommitBoundary :=
  if snapshot.version.val = 2 ^ 64 - 1 then some ⟨TransferBankRecovery.initial, none⟩
  else snapshot.root.bind fun root =>
    (TransferAuthenticatedBoundarySource01.readCommittedBoundary snapshot.authentication snapshot.reader
      snapshot.project snapshot.state root).map fun boundary => ⟨boundary, some root⟩

def recoveryInput {O : Type} (io : Io O) (store : Store) : Store := (io.lock store).store

def recovered {O : Type} (io : Io O) (store : Store) (boundary : CommitBoundary) : TransferBankRecovery.Outcome :=
  let current := recoveryInput io store
  TransferCapturedRecovery01.recoverCaptured current (io.recoveryIo current) boundary.nullifiers
    (io.readIntent current) (io.readHistory current)

def recoverCurrent {O : Type} (io : Io O) (store : Store) : Outcome :=
  match selected io.snapshot with
  | none => ⟨.interrupted, store, false⟩
  | some boundary =>
    if (io.lock store).acquired = true then
      let result := recovered io store boundary
      if result.error = none then ⟨.ready boundary, result.store, true⟩
      else ⟨.interrupted, result.store, false⟩
    else ⟨.interrupted, recoveryInput io store, false⟩

theorem selected_boundary_derives_default_version_or_actual_authenticated_snapshot_read {O : Type}
    (snapshot : Snapshot O) (boundary : CommitBoundary) (success : selected snapshot = some boundary) :
    (snapshot.version.val = 2 ^ 64 - 1 ∧ boundary = ⟨TransferBankRecovery.initial, none⟩) ∨
      (snapshot.version.val ≠ 2 ^ 64 - 1 ∧ ∃ root actual,
        snapshot.root = some root ∧
        TransferAuthenticatedBoundarySource01.readCommittedBoundary snapshot.authentication snapshot.reader
          snapshot.project snapshot.state root = some actual ∧ boundary = ⟨actual, some root⟩) := by
  by_cases uninitialized : snapshot.version.val = 2 ^ 64 - 1
  · exact Or.inl ⟨uninitialized, (Option.some.inj (by simpa only [selected, if_pos uninitialized] using success)).symm⟩
  · cases rootRead : snapshot.root with
    | none => simp only [selected, if_neg uninitialized, rootRead, Option.bind_none] at success; cases success
    | some root =>
      cases actualRead : TransferAuthenticatedBoundarySource01.readCommittedBoundary snapshot.authentication snapshot.reader snapshot.project snapshot.state root with
      | none => simp only [selected, if_neg uninitialized, rootRead, Option.bind_some, actualRead, Option.map_none] at success; cases success
      | some actual =>
        have same : boundary = ⟨actual, some root⟩ := (Option.some.inj (by
          simpa only [selected, if_neg uninitialized, rootRead, Option.bind_some, actualRead, Option.map_some] using success)).symm
        exact Or.inr ⟨uninitialized, root, actual, rfl, rfl, same⟩

theorem clean_captured_recovery_derives_final_checks_without_assuming_health_or_restoration
    (store : Store) (io : TransferBankRecovery.Io) (boundary : TransferReadback.Boundary)
    (intent : TransferBankRecovery.IntentRead) (history : TransferBankRecovery.HistoryRead)
    (clean : (TransferCapturedRecovery01.recoverCaptured store io boundary intent history).error = none) :
    (TransferCapturedRecovery01.recoverCaptured store io boundary intent history).store.ready = true ∧
      (TransferCapturedRecovery01.recoverCaptured store io boundary intent history).store.actualRoots = boundary.roots ∧
      (TransferCapturedRecovery01.recoverCaptured store io boundary intent history).store.boundary = some boundary ∧
      boundary.roots.length = 16 ∧ TransferBankRecovery.HistoryValid boundary history ∧
      (TransferCapturedRecovery01.recoverCaptured store io boundary intent history).store.healthy = io.healthyAfter := by
  cases observation : (TransferCapturedRecovery01.prepareCaptured io store.actualRoots boundary intent).error with
  | some error => simp only [TransferCapturedRecovery01.recoverCaptured, observation, TransferBankRecovery.unavailable] at clean; cases clean
  | none =>
    have finished : TransferBankRecovery.finish {store with healthy := io.healthyAfter}
        (TransferCapturedRecovery01.prepareCaptured io store.actualRoots boundary intent).roots boundary history =
        TransferCapturedRecovery01.recoverCaptured store io boundary intent history := by
      simp only [TransferCapturedRecovery01.recoverCaptured, observation]
    have checks := TransferBankRecovery.finish_success _ _ _ _ _ finished clean
    exact ⟨checks.2.1, checks.2.2.1, checks.2.2.2.1, checks.1.2.1, checks.1.2.2, checks.2.2.2.2⟩

theorem whole_current_recovery_success_derives_selected_boundary_actual_lock_and_observed_physical_state {O : Type}
    (io : Io O) (store : Store) (success : (recoverCurrent io store).succeeded = true) :
    ∃ boundary, selected io.snapshot = some boundary ∧ (io.lock store).acquired = true ∧
      (recovered io store boundary).error = none ∧ (recoverCurrent io store).phase = .ready boundary ∧
      (recoverCurrent io store).store = (recovered io store boundary).store ∧
      (recoverCurrent io store).store.ready = true ∧
      (recoverCurrent io store).store.actualRoots = boundary.nullifiers.roots ∧
      (recoverCurrent io store).store.boundary = some boundary.nullifiers ∧ boundary.nullifiers.roots.length = 16 ∧
      TransferBankRecovery.HistoryValid boundary.nullifiers (io.readHistory (recoveryInput io store)) ∧
      (recoverCurrent io store).store.healthy = (io.recoveryIo (recoveryInput io store)).healthyAfter := by
  cases boundaryRead : selected io.snapshot with
  | none => simp only [recoverCurrent, boundaryRead] at success; cases success
  | some boundary =>
    by_cases locked : (io.lock store).acquired = true
    · by_cases clean : (recovered io store boundary).error = none
      · have same : (recoverCurrent io store).store = (recovered io store boundary).store := by
          simp only [recoverCurrent, boundaryRead, if_pos locked, if_pos clean]
        have checks := clean_captured_recovery_derives_final_checks_without_assuming_health_or_restoration
          (recoveryInput io store) (io.recoveryIo (recoveryInput io store)) boundary.nullifiers
          (io.readIntent (recoveryInput io store)) (io.readHistory (recoveryInput io store)) clean
        refine ⟨boundary, rfl, locked, clean, ?_, same, ?_⟩
        · simp only [recoverCurrent, boundaryRead, if_pos locked, if_pos clean]
        · rw [same]; exact checks
      · simp only [recoverCurrent, boundaryRead, if_pos locked, if_neg clean] at success; cases success
    · simp only [recoverCurrent, boundaryRead, if_neg locked] at success; cases success

theorem unavailable_noninitial_snapshot_root_refuses_before_lock_and_recovery {O : Type}
    (io : Io O) (store : Store) (initialized : io.snapshot.version.val ≠ 2 ^ 64 - 1) (missing : io.snapshot.root = none) :
    recoverCurrent io store = ⟨.interrupted, store, false⟩ := by
  simp only [recoverCurrent, selected, if_neg initialized, missing, Option.bind_none]

theorem failed_current_recovery_keeps_owner_interrupted_and_actual_recovery_progress {O : Type}
    (io : Io O) (store : Store) (boundary : CommitBoundary) (selectedBoundary : selected io.snapshot = some boundary)
    (locked : (io.lock store).acquired = true) (failed : (recovered io store boundary).error ≠ none) :
    recoverCurrent io store = ⟨.interrupted, (recovered io store boundary).store, false⟩ := by
  simp only [recoverCurrent, selectedBoundary, if_pos locked, if_neg failed]

set_option pp.all true in
#check @Snapshot
#print axioms Snapshot
set_option pp.all true in
#check @LockResult
#print axioms LockResult
set_option pp.all true in
#check @Io
#print axioms Io
set_option pp.all true in
#check @Outcome
#print axioms Outcome
set_option pp.all true in
#check @selected
#print axioms selected
set_option pp.all true in
#check @recoveryInput
#print axioms recoveryInput
set_option pp.all true in
#check @recovered
#print axioms recovered
set_option pp.all true in
#check @recoverCurrent
#print axioms recoverCurrent
set_option pp.all true in
#check @selected_boundary_derives_default_version_or_actual_authenticated_snapshot_read
#print axioms selected_boundary_derives_default_version_or_actual_authenticated_snapshot_read
set_option pp.all true in
#check @clean_captured_recovery_derives_final_checks_without_assuming_health_or_restoration
#print axioms clean_captured_recovery_derives_final_checks_without_assuming_health_or_restoration
set_option pp.all true in
#check @whole_current_recovery_success_derives_selected_boundary_actual_lock_and_observed_physical_state
#print axioms whole_current_recovery_success_derives_selected_boundary_actual_lock_and_observed_physical_state
set_option pp.all true in
#check @unavailable_noninitial_snapshot_root_refuses_before_lock_and_recovery
#print axioms unavailable_noninitial_snapshot_root_refuses_before_lock_and_recovery
set_option pp.all true in
#check @failed_current_recovery_keeps_owner_interrupted_and_actual_recovery_progress
#print axioms failed_current_recovery_keeps_owner_interrupted_and_actual_recovery_progress
end ShielddSecurity.TransferWriterRecoverCurrent01
