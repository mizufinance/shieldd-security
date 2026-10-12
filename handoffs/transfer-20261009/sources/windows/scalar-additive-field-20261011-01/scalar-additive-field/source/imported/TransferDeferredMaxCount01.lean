import ShielddSecurity.TransferDeferredCountFlush01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferDeferredMaxCount01
open TransferStateDelta TransferIndexWriterModel01 TransferDeferredCountWalk01

/-! Exact max-count parent bytes exclude every nonempty successful deferred
walk, for arbitrary conversion and read availability. Earlier failures are not
semantic overflow controls. Queue take then error preserves the parent and
drains the queue; empty retry cannot reconstruct entries. Rust/private fault
reachability, byte/key/store/Host/native/durability remain interfaces. -/

theorem max_count_excludes_nonempty_walk_success {O E A : Type}
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (height : Nat) (parent : State O) (actions : List A) (cache : Cache O E)
    (nonempty : actions ≠ [])
    (storedCount : parent.nonverifiable (keys.count height) = some TransferOrdinaryMaxCount01.maxBytes) :
    TransferDeferredQueueSourceModel01.walk (queueWriter keys convert available parent)
      height empty actions ≠ .ok cache := by
  intro success
  have observed : countObservation TransferIndexCountCodec01.codec
      ((applyCache parent (empty (E := E))).nonverifiable (keys.count height)) =
        some (⟨2 ^ 64 - 1, by decide⟩ : Ordinal) := by
    rw [apply_empty, storedCount]
    exact TransferOrdinaryMaxCount01.max_bytes_decode
  have bound := successful_walk_cannot_wrap_u64 keys convert available height parent actions empty cache
    (⟨2 ^ 64 - 1, by decide⟩ : Ordinal) observed success
  change 2 ^ 64 - 1 + actions.length < 2 ^ 64 at bound
  have positive : 0 < actions.length := by
    cases actions with
    | nil => exact False.elim (nonempty rfl)
    | cons action rest => simp only [List.length_cons]; omega
  have modulusPositive : 0 < (2 : Nat) ^ 64 := by decide
  omega

theorem max_count_flush_derives_failure_parent_and_drained_queue {O E A : Type}
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (height : Nat) (parent : State O) (actions : List A)
    (nonempty : actions ≠ [])
    (storedCount : parent.nonverifiable (keys.count height) = some TransferOrdinaryMaxCount01.maxBytes) :
    ∃ error : IndexError,
      TransferDeferredQueueSourceModel01.flush (queueWriter (E := E) keys convert available parent)
        true true (some height) parent actions = TransferDeferredQueueSourceModel01.refused parent [] (.index error) := by
  cases walked : TransferDeferredQueueSourceModel01.walk (queueWriter (E := E) keys convert available parent)
      height empty actions with
  | error error =>
    exact ⟨error, TransferDeferredQueueSourceModel01.index_failure_discards_child_and_consumes_queue
      (queueWriter keys convert available parent) height parent actions error nonempty walked⟩
  | ok cache =>
    exact False.elim ((max_count_excludes_nonempty_walk_success keys convert available height parent actions cache
      nonempty storedCount) walked)

theorem max_count_same_instance_retry_cannot_reconstruct_queue {O E A : Type}
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (height : Nat) (parent : State O) (actions : List A)
    (nonempty : actions ≠ [])
    (storedCount : parent.nonverifiable (keys.count height) = some TransferOrdinaryMaxCount01.maxBytes)
    (retryPut : TransferDeferredQueueSourceModel01.IndexWriter O E A IndexError)
    (retryExclusive : Bool) (retryHeight : Option Nat) :
    let interrupted := TransferDeferredQueueSourceModel01.flush (queueWriter (E := E) keys convert available parent)
      true true (some height) parent actions
    TransferDeferredQueueSourceModel01.flush retryPut true retryExclusive retryHeight interrupted.parent interrupted.queued =
      TransferDeferredQueueSourceModel01.unchanged parent [] := by
  obtain ⟨error, failed⟩ := max_count_flush_derives_failure_parent_and_drained_queue (E := E)
    keys convert available height parent actions nonempty storedCount
  dsimp only
  rw [failed]
  exact TransferDeferredQueueSourceModel01.empty_queue_shortcuts_all_fallible_calls retryPut true retryExclusive retryHeight parent

set_option pp.all true in
#check @max_count_excludes_nonempty_walk_success
#print axioms max_count_excludes_nonempty_walk_success
set_option pp.all true in
#check @max_count_flush_derives_failure_parent_and_drained_queue
#print axioms max_count_flush_derives_failure_parent_and_drained_queue
set_option pp.all true in
#check @max_count_same_instance_retry_cannot_reconstruct_queue
#print axioms max_count_same_instance_retry_cannot_reconstruct_queue
end ShielddSecurity.TransferDeferredMaxCount01
