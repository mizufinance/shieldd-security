import ShielddSecurity.TransferCapturedRecovery01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferTakeCommitState01
open TransferStateDelta
open TransferIndexWriterModel01 (Keys Encoded IndexError)
open TransferNullifierBatchSource01 (Pending)

/-! Source App::take_commit_state checks actual ensureSealed, performs concrete
deferred flush, then installs a fresh snapshot with the typed reader and tries
to unwrap the previous Arc. Failed unwrap restores the post-flush previous
state, not the state before flush. Actual unwrap success is an independently
observed primitive branch. Rust Arc exact-value/no-hidden-alias semantics,
typed object getter/Clone/reader/key/snapshot/concurrency/ownership remain
native library correspondence interfaces, not consequences of this model.
Fresh replacement drops old disposable objects; returned state is the exact
post-flush state. No native/control/durability/full certification inferred. -/

structure Io (O : Type) where
  latestSnapshot : State O → State O
  readerKey : Nat
  reader : O
  unwrapSucceeded : State O → Bool

structure Outcome (O A : Type) where
  active : State O
  queued : List A
  returned : Option (State O)

def replacement {O : Type} (io : Io O) (current : State O) : State O :=
  ⟨(io.latestSnapshot current).verifiable, (io.latestSnapshot current).nonverifiable,
    fun key => if key = io.readerKey then some io.reader else none⟩

def flushFor {O E A : Type} (keys : Keys) (convert : A → Option Encoded)
    (available : Delta O E → Nat → Bool) (deferred exclusive : Bool) (height : Option Nat)
    (parent : State O) (queued : List A) : TransferDeferredQueueSourceModel01.Outcome O E A IndexError :=
  TransferDeferredQueueSourceModel01.flush
    (TransferDeferredCountWalk01.queueWriter keys convert available parent) deferred exclusive height parent queued

def takeState {O E A : Type} (io : Io O) (decode : O → Pending) (pendingKey : Nat)
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (deferred exclusive : Bool) (height : Option Nat) (parent : State O) (queued : List A) : Outcome O A :=
  match TransferPendingSealSource01.ensureSealed decode pendingKey ⟨parent, (empty : Cache O E)⟩ with
  | .error _ => ⟨parent, queued, none⟩
  | .ok () =>
    let flushed := flushFor keys convert available deferred exclusive height parent queued
    match flushed.error with
    | some _ => ⟨flushed.parent, flushed.queued, none⟩
    | none => if io.unwrapSucceeded flushed.parent = true then
        ⟨replacement io flushed.parent, flushed.queued, some flushed.parent⟩
      else ⟨flushed.parent, flushed.queued, none⟩

theorem whole_transfer_success_derives_sealed_flush_exclusive_and_exact_transferred_state {O E A : Type}
    (io : Io O) (decode : O → Pending) (pendingKey : Nat)
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (deferred exclusive : Bool) (height : Option Nat) (parent returned : State O) (queued : List A)
    (success : (takeState io decode pendingKey keys convert available deferred exclusive height parent queued).returned = some returned) :
    TransferPendingSealSource01.ensureSealed decode pendingKey ⟨parent, (empty : Cache O E)⟩ = .ok () ∧
      (flushFor keys convert available deferred exclusive height parent queued).error = none ∧
      io.unwrapSucceeded (flushFor keys convert available deferred exclusive height parent queued).parent = true ∧
      returned = (flushFor keys convert available deferred exclusive height parent queued).parent ∧
      (takeState io decode pendingKey keys convert available deferred exclusive height parent queued).active =
        replacement io (flushFor keys convert available deferred exclusive height parent queued).parent ∧
      (takeState io decode pendingKey keys convert available deferred exclusive height parent queued).queued =
        (flushFor keys convert available deferred exclusive height parent queued).queued := by
  cases ensured : TransferPendingSealSource01.ensureSealed decode pendingKey ⟨parent, (empty : Cache O E)⟩ with
  | error error => simp only [takeState, ensured] at success; cases success
  | ok unit =>
    cases unit
    cases flushed : (flushFor keys convert available deferred exclusive height parent queued).error with
    | some error => simp only [takeState, ensured, flushed] at success; cases success
    | none =>
      by_cases unwrapped : io.unwrapSucceeded (flushFor keys convert available deferred exclusive height parent queued).parent = true
      · have same : returned = (flushFor keys convert available deferred exclusive height parent queued).parent :=
          (Option.some.inj (by simpa only [takeState, ensured, flushed, if_pos unwrapped] using success)).symm
        exact ⟨rfl, rfl, unwrapped, same,
          by simp only [takeState, ensured, flushed, if_pos unwrapped],
          by simp only [takeState, ensured, flushed, if_pos unwrapped]⟩
      · simp only [takeState, ensured, flushed, if_neg unwrapped] at success; cases success

theorem failed_unwrap_restores_post_flush_state_and_current_queue {O E A : Type}
    (io : Io O) (decode : O → Pending) (pendingKey : Nat)
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (deferred exclusive : Bool) (height : Option Nat) (parent : State O) (queued : List A)
    (ensured : TransferPendingSealSource01.ensureSealed decode pendingKey ⟨parent, (empty : Cache O E)⟩ = .ok ())
    (flushed : (flushFor keys convert available deferred exclusive height parent queued).error = none)
    (shared : io.unwrapSucceeded (flushFor keys convert available deferred exclusive height parent queued).parent = false) :
    takeState io decode pendingKey keys convert available deferred exclusive height parent queued =
      ⟨(flushFor keys convert available deferred exclusive height parent queued).parent,
        (flushFor keys convert available deferred exclusive height parent queued).queued, none⟩ := by
  simp only [takeState, ensured, flushed, shared, Bool.false_eq_true, if_false]

theorem ensure_failure_precedes_flush_and_replacement {O E A : Type}
    (io : Io O) (decode : O → Pending) (pendingKey : Nat)
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (deferred exclusive : Bool) (height : Option Nat) (parent : State O) (queued : List A)
    (error : TransferPendingSealSource01.SealError)
    (failed : TransferPendingSealSource01.ensureSealed decode pendingKey ⟨parent, (empty : Cache O E)⟩ = .error error) :
    takeState io decode pendingKey keys convert available deferred exclusive height parent queued = ⟨parent, queued, none⟩ := by
  simp only [takeState, failed]

theorem concrete_index_failure_keeps_delivered_parent_consumes_queue_and_refuses_transfer {O E A : Type}
    (io : Io O) (decode : O → Pending) (pendingKey : Nat)
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (height : Nat) (parent : State O) (queued : List A) (error : IndexError)
    (ensured : TransferPendingSealSource01.ensureSealed decode pendingKey ⟨parent, (empty : Cache O E)⟩ = .ok ())
    (nonempty : queued ≠ [])
    (failed : TransferDeferredQueueSourceModel01.walk
      (TransferDeferredCountWalk01.queueWriter keys convert available parent) height empty queued = .error error) :
    takeState io decode pendingKey keys convert available true true (some height) parent queued = ⟨parent, [], none⟩ := by
  have flushed := TransferDeferredQueueSourceModel01.index_failure_discards_child_and_consumes_queue
    (TransferDeferredCountWalk01.queueWriter keys convert available parent) height parent queued error nonempty failed
  simp only [takeState, ensured, flushFor, flushed, TransferDeferredQueueSourceModel01.refused]

theorem successful_nonempty_transferred_state_retains_original_pending_objects {O E A : Type}
    (io : Io O) (decode : O → Pending) (pendingKey : Nat)
    (keys : Keys) (convert : A → Option Encoded) (available : Delta O E → Nat → Bool)
    (height : Nat) (parent returned : State O) (queued : List A) (initial : TransferIndexWriterModel01.Ordinal)
    (nonempty : queued ≠ [])
    (observed : TransferIndexWriterModel01.countObservation TransferIndexCountCodec01.codec
      (parent.nonverifiable (keys.count height)) = some initial)
    (success : (takeState io decode pendingKey keys convert available true true (some height) parent queued).returned = some returned) :
    returned.objects = parent.objects ∧ returned.verifiable = parent.verifiable ∧
      (takeState io decode pendingKey keys convert available true true (some height) parent queued).queued = [] := by
  obtain ⟨_, clean, _, same, _, queue⟩ := whole_transfer_success_derives_sealed_flush_exclusive_and_exact_transferred_state
    io decode pendingKey keys convert available true true (some height) parent returned queued success
  have flushed := TransferDeferredCountFlush01.successful_nonempty_flush_derives_count_queue_and_effects
    keys convert available height parent queued initial nonempty observed clean
  obtain ⟨_, _, _, _, verifiable, objects, emptyQueue, _⟩ := flushed
  exact ⟨by rw [same]; exact objects, by rw [same]; exact verifiable, queue.trans emptyQueue⟩

theorem replacement_contains_only_current_reader_and_latest_snapshot_bytes {O : Type}
    (io : Io O) (current : State O) :
    (replacement io current).verifiable = (io.latestSnapshot current).verifiable ∧
      (replacement io current).nonverifiable = (io.latestSnapshot current).nonverifiable ∧
      (replacement io current).objects io.readerKey = some io.reader ∧
      ∀ key, key ≠ io.readerKey → (replacement io current).objects key = none := by
  exact ⟨rfl, rfl, by simp only [replacement, if_true], fun _ different => by simp only [replacement, if_neg different]⟩

set_option pp.all true in
#check @Io
#print axioms Io
set_option pp.all true in
#check @Outcome
#print axioms Outcome
set_option pp.all true in
#check @replacement
#print axioms replacement
set_option pp.all true in
#check @flushFor
#print axioms flushFor
set_option pp.all true in
#check @takeState
#print axioms takeState
set_option pp.all true in
#check @whole_transfer_success_derives_sealed_flush_exclusive_and_exact_transferred_state
#print axioms whole_transfer_success_derives_sealed_flush_exclusive_and_exact_transferred_state
set_option pp.all true in
#check @failed_unwrap_restores_post_flush_state_and_current_queue
#print axioms failed_unwrap_restores_post_flush_state_and_current_queue
set_option pp.all true in
#check @ensure_failure_precedes_flush_and_replacement
#print axioms ensure_failure_precedes_flush_and_replacement
set_option pp.all true in
#check @concrete_index_failure_keeps_delivered_parent_consumes_queue_and_refuses_transfer
#print axioms concrete_index_failure_keeps_delivered_parent_consumes_queue_and_refuses_transfer
set_option pp.all true in
#check @successful_nonempty_transferred_state_retains_original_pending_objects
#print axioms successful_nonempty_transferred_state_retains_original_pending_objects
set_option pp.all true in
#check @replacement_contains_only_current_reader_and_latest_snapshot_bytes
#print axioms replacement_contains_only_current_reader_and_latest_snapshot_bytes
end ShielddSecurity.TransferTakeCommitState01
