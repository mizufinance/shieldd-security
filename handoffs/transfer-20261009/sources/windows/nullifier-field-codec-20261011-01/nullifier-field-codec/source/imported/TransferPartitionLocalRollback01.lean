import ShielddSecurity.TransferByteKeyCache01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferPartitionLocalRollback01
open TransferBankRecovery (Io Physical Error IntentRead HistoryRead)
open TransferReadback (Store Boundary)
/-! Partition-local model rollback updates only its indexed root, retaining
an independently supplied own root and possible error. This derives the
forward frame used by captured-root recovery without supplying that frame
as a desired postcondition. No own-root restoration or success is assumed.
Actual NOMT handle isolation/concurrent root observations/locks/health/native
trace/filesystem/crash durability correspondence stays explicit. -/

def installPartitionLocalRollback
    (rootAfter : Nat → List Nat → Nat) (errorAfter : Nat → List Nat → Option Error) (base : Io) : Io :=
  {base with rollback := fun index current => ⟨current.set index (rootAfter index current), errorAfter index current⟩}

theorem indexed_rollback_preserves_every_other_root_even_on_error
    (rootAfter : Nat → List Nat → Nat) (errorAfter : Nat → List Nat → Option Error) (base : Io)
    (index other : Nat) (current : List Nat) (different : index ≠ other) :
    ((installPartitionLocalRollback rootAfter errorAfter base).rollback index current).roots.getD other 0 =
      current.getD other 0 := by
  change (current.set index (rootAfter index current)).getD other 0 = current.getD other 0
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne different]

theorem partition_local_rollback_derives_forward_partition_frames
    (rootAfter : Nat → List Nat → Nat) (errorAfter : Nat → List Nat → Option Error) (base : Io) :
    TransferCapturedRecovery01.ForwardPartitionFrames (installPartitionLocalRollback rootAfter errorAfter base) := by
  intro index current later strictlyLater _
  exact indexed_rollback_preserves_every_other_root_even_on_error rootAfter errorAfter base index later current
    (Nat.ne_of_lt strictlyLater)

theorem partition_local_captured_recovery_reuses_original_complete_result
    (rootAfter : Nat → List Nat → Nat) (errorAfter : Nat → List Nat → Option Error) (base : Io)
    (store : Store) (committed : Boundary) (intent : IntentRead) (history : HistoryRead) :
    TransferCapturedRecovery01.recoverCaptured store (installPartitionLocalRollback rootAfter errorAfter base) committed intent history =
      TransferBankRecovery.recover store (installPartitionLocalRollback rootAfter errorAfter base) committed intent history :=
  TransferCapturedRecovery01.captured_recovery_reuses_original_result_under_explicit_partition_frames
    store (installPartitionLocalRollback rootAfter errorAfter base) committed intent history
    (partition_local_rollback_derives_forward_partition_frames rootAfter errorAfter base)

set_option pp.all true in
#check @installPartitionLocalRollback
#print axioms installPartitionLocalRollback
set_option pp.all true in
#check @indexed_rollback_preserves_every_other_root_even_on_error
#print axioms indexed_rollback_preserves_every_other_root_even_on_error
set_option pp.all true in
#check @partition_local_rollback_derives_forward_partition_frames
#print axioms partition_local_rollback_derives_forward_partition_frames
set_option pp.all true in
#check @partition_local_captured_recovery_reuses_original_complete_result
#print axioms partition_local_captured_recovery_reuses_original_complete_result
end ShielddSecurity.TransferPartitionLocalRollback01
