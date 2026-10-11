import ShielddSecurity.TransferStatefulParticipantRecovery01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferCapturedRecovery01
open TransferReadback (Store Boundary)
open TransferBankRecovery (Io Physical IntentRead HistoryRead Outcome TransitionValid KnownPartitions)

/-! Rust captures actual_roots once for partition eligibility and rollback
selection. The source recurrence below uses that fixed initial vector, threading
independent actual callback outcomes only as physical progress. The original
changing-vector recurrence is reusable only under a stated forward partition
frame contract: a successful rollback of an earlier partition cannot alter a
later partition. This contract does not assert that rollback restores its own
root, succeeds, keeps health true, or provides durability. It is a native NOMT/
locking/observation correspondence obligation, not an axiom proved by hashes.
Final physical observations, current poison health, typed roots/serde/file IO,
ownership and source-to-runtime execution correspondence remain interfaces. -/

def ForwardPartitionFrames (io : Io) : Prop :=
  ∀ index current later, index < later → (io.rollback index current).error = none →
    (io.rollback index current).roots.getD later 0 = current.getD later 0

def capturedRollbacks (io : Io) (initial wanted : List Nat) : Nat → Nat → List Nat → Physical
  | _, 0, current => ⟨current, none⟩
  | index, remaining + 1, current =>
    if initial.getD index 0 = wanted.getD index 0 then
      capturedRollbacks io initial wanted (index + 1) remaining current
    else
      let observed := io.rollback index current
      match observed.error with
      | some _ => ⟨observed.roots, some .rollback⟩
      | none => capturedRollbacks io initial wanted (index + 1) remaining observed.roots

def prepareCaptured (io : Io) (actual : List Nat) (committed : Boundary) (intent : IntentRead) : Physical :=
  match intent with
  | .failed => ⟨actual, some .intentRead⟩
  | .missing => if actual = committed.roots then ⟨actual, none⟩ else ⟨actual, some .rootMismatch⟩
  | .record record =>
      if ¬ TransitionValid record then ⟨actual, some .invalidIntent⟩
      else if ¬ (committed = record.previous ∨ committed = record.next) then ⟨actual, some .boundaryConflict⟩
      else if ¬ KnownPartitions actual record then ⟨actual, some .unknownPartition⟩
      else if committed = record.previous then
        TransferBankRecovery.cleanIntent io committed (capturedRollbacks io actual committed.roots 0 16 actual)
      else if actual ≠ committed.roots then ⟨actual, some .nextLagging⟩
      else if io.retained = false then ⟨actual, some .retain⟩
      else TransferBankRecovery.cleanIntent io committed ⟨actual, none⟩

def recoverCaptured (store : Store) (io : Io) (committed : Boundary) (intent : IntentRead) (history : HistoryRead) : Outcome :=
  let observed := prepareCaptured io store.actualRoots committed intent
  match observed.error with
  | some error => TransferBankRecovery.unavailable {store with healthy := io.healthyAfter} observed.roots error
  | none => TransferBankRecovery.finish {store with healthy := io.healthyAfter} observed.roots committed history

theorem captured_rollbacks_equal_original_under_forward_partition_frames
    (io : Io) (initial wanted : List Nat) (index remaining : Nat) (current : List Nat)
    (frames : ForwardPartitionFrames io)
    (tailSame : ∀ later, index ≤ later → current.getD later 0 = initial.getD later 0) :
    capturedRollbacks io initial wanted index remaining current =
      TransferBankRecovery.rollbacks io wanted index remaining current := by
  induction remaining generalizing index current with
  | zero => rfl
  | succ remaining ih =>
    have atIndex := tailSame index (Nat.le_refl index)
    by_cases matched : initial.getD index 0 = wanted.getD index 0
    · have currentMatch : current.getD index 0 = wanted.getD index 0 := atIndex.trans matched
      rw [capturedRollbacks, if_pos matched, TransferBankRecovery.rollbacks, if_pos currentMatch]
      apply ih
      intro later forward
      exact tailSame later (Nat.le_trans (Nat.le_succ index) forward)
    · have currentMismatch : current.getD index 0 ≠ wanted.getD index 0 := by
        intro equal
        exact matched (atIndex.symm.trans equal)
      rw [capturedRollbacks, if_neg matched, TransferBankRecovery.rollbacks, if_neg currentMismatch]
      cases observed : (io.rollback index current).error with
      | some error => simp only [observed]
      | none =>
        simp only [observed]
        apply ih
        intro later forward
        have strictlyLater : index < later := Nat.lt_of_lt_of_le (Nat.lt_succ_self index) forward
        exact (frames index current later strictlyLater observed).trans
          (tailSame later (Nat.le_trans (Nat.le_succ index) forward))

theorem failed_captured_rollback_retains_observed_progress_without_suffix
    (io : Io) (initial wanted current : List Nat) (index remaining : Nat) (error : TransferBankRecovery.Error)
    (changed : initial.getD index 0 ≠ wanted.getD index 0)
    (failed : (io.rollback index current).error = some error) :
    capturedRollbacks io initial wanted index (remaining + 1) current =
      ⟨(io.rollback index current).roots, some .rollback⟩ := by
  simp only [capturedRollbacks, if_neg changed, failed]

theorem captured_prepare_equals_original_only_under_forward_partition_contract
    (io : Io) (actual : List Nat) (committed : Boundary) (intent : IntentRead)
    (frames : ForwardPartitionFrames io) :
    prepareCaptured io actual committed intent = TransferBankRecovery.prepare io actual committed intent := by
  cases intent with
  | failed => rfl
  | missing => rfl
  | record record =>
    have same := captured_rollbacks_equal_original_under_forward_partition_frames io actual committed.roots 0 16 actual frames
      (fun _ _ => rfl)
    simp only [prepareCaptured, TransferBankRecovery.prepare, same]

theorem captured_recovery_reuses_original_result_under_explicit_partition_frames
    (store : Store) (io : Io) (committed : Boundary) (intent : IntentRead) (history : HistoryRead)
    (frames : ForwardPartitionFrames io) :
    recoverCaptured store io committed intent history = TransferBankRecovery.recover store io committed intent history := by
  simp only [recoverCaptured, TransferBankRecovery.recover,
    captured_prepare_equals_original_only_under_forward_partition_contract io store.actualRoots committed intent frames]

set_option pp.all true in
#check @ForwardPartitionFrames
#print axioms ForwardPartitionFrames
set_option pp.all true in
#check @capturedRollbacks
#print axioms capturedRollbacks
set_option pp.all true in
#check @prepareCaptured
#print axioms prepareCaptured
set_option pp.all true in
#check @recoverCaptured
#print axioms recoverCaptured
set_option pp.all true in
#check @captured_rollbacks_equal_original_under_forward_partition_frames
#print axioms captured_rollbacks_equal_original_under_forward_partition_frames
set_option pp.all true in
#check @failed_captured_rollback_retains_observed_progress_without_suffix
#print axioms failed_captured_rollback_retains_observed_progress_without_suffix
set_option pp.all true in
#check @captured_prepare_equals_original_only_under_forward_partition_contract
#print axioms captured_prepare_equals_original_only_under_forward_partition_contract
set_option pp.all true in
#check @captured_recovery_reuses_original_result_under_explicit_partition_frames
#print axioms captured_recovery_reuses_original_result_under_explicit_partition_frames
end ShielddSecurity.TransferCapturedRecovery01
