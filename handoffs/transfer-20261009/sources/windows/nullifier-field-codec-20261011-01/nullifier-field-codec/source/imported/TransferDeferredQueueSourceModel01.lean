import ShielddSecurity.TransferStateDelta

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferDeferredQueueSourceModel01

open TransferStateDelta

/-! Functional source-order model for `flush_deferred_block_transactions`.
The parent may already contain genuinely delivered effects. Child index writes
are separate caches; mode/empty, exclusive acquisition and height read precede
the queue take. Fallible index writes follow it. Rust cache/container/ownership
refinement and the native callback contracts remain separate obligations. -/

inductive Failure (X : Type) where
  | exclusive
  | height
  | index (error : X)

structure Outcome (O E T X : Type) where
  parent : State O
  queued : List T
  events : List E
  error : Option (Failure X)

abbrev IndexWriter (O E T X : Type) := Nat → Cache O E → T → Except X (Cache O E)

def walk {O E T X : Type} (put : IndexWriter O E T X) (height : Nat) :
    Cache O E → List T → Except X (Cache O E)
  | child, [] => .ok child
  | child, tx :: rest => match put height child tx with
    | .error error => .error error
    | .ok next => walk put height next rest

def unchanged {O E T X : Type} (parent : State O) (queued : List T) : Outcome O E T X :=
  ⟨parent, queued, [], none⟩

def refused {O E T X : Type} (parent : State O) (queued : List T)
    (error : Failure X) : Outcome O E T X :=
  ⟨parent, queued, [], some error⟩

theorem nonempty_test {T : Type} (queued : List T) (nonempty : queued ≠ []) :
    queued.isEmpty = false := by
  cases queued with
  | nil => exact False.elim (nonempty rfl)
  | cons _ _ => rfl

def flush {O E T X : Type} (put : IndexWriter O E T X) (deferred exclusive : Bool)
    (height : Option Nat) (parent : State O) (queued : List T) : Outcome O E T X :=
  if deferred = false then unchanged parent queued
  else if queued.isEmpty = true then unchanged parent []
  else if exclusive = false then refused parent queued .exclusive
  else match height with
    | none => refused parent queued .height
    | some h => match walk put h empty queued with
      | .error error => refused parent [] (.index error)
      | .ok child => ⟨applyCache parent child, [], child.events, none⟩

theorem other_mode_preserves_queue {O E T X : Type} (put : IndexWriter O E T X)
    (exclusive : Bool) (height : Option Nat) (parent : State O) (queued : List T) :
    flush put false exclusive height parent queued = unchanged parent queued := by
  rfl

theorem empty_queue_shortcuts_all_fallible_calls {O E T X : Type}
    (put : IndexWriter O E T X) (deferred exclusive : Bool) (height : Option Nat) (parent : State O) :
    flush put deferred exclusive height parent [] = unchanged parent [] := by
  cases deferred <;> rfl

theorem exclusive_failure_precedes_take {O E T X : Type} (put : IndexWriter O E T X)
    (height : Option Nat) (parent : State O) (queued : List T) (nonempty : queued ≠ []) :
    flush put true false height parent queued = refused parent queued .exclusive := by
  unfold flush
  rw [nonempty_test queued nonempty]
  rfl

theorem height_failure_precedes_take {O E T X : Type} (put : IndexWriter O E T X)
    (parent : State O) (queued : List T) (nonempty : queued ≠ []) :
    flush put true true none parent queued = refused parent queued .height := by
  unfold flush
  rw [nonempty_test queued nonempty]
  rfl

theorem post_take_dispatch {O E T X : Type} (put : IndexWriter O E T X)
    (height : Nat) (parent : State O) (queued : List T) (nonempty : queued ≠ []) :
    flush put true true (some height) parent queued =
      match walk put height empty queued with
      | .error error => refused parent [] (.index error)
      | .ok child => ⟨applyCache parent child, [], child.events, none⟩ := by
  unfold flush
  rw [nonempty_test queued nonempty]
  rfl

theorem index_failure_discards_child_and_consumes_queue {O E T X : Type}
    (put : IndexWriter O E T X) (height : Nat) (parent : State O) (queued : List T)
    (error : X) (nonempty : queued ≠ [])
    (failed : walk put height empty queued = .error error) :
    flush put true true (some height) parent queued = refused parent [] (.index error) := by
  rw [post_take_dispatch put height parent queued nonempty, failed]

theorem index_failure_preserves_preexisting_effect_state {O E T X : Type}
    (put : IndexWriter O E T X) (height : Nat) (parent : State O) (queued : List T)
    (error : X) (nonempty : queued ≠ [])
    (failed : walk put height empty queued = .error error) :
    (flush put true true (some height) parent queued).parent = parent ∧
      (flush put true true (some height) parent queued).queued = [] ∧
      (flush put true true (some height) parent queued).events = [] := by
  rw [index_failure_discards_child_and_consumes_queue put height parent queued error nonempty failed]
  exact ⟨rfl, rfl, rfl⟩

theorem same_instance_retry_cannot_recreate_consumed_queue {O E T X : Type}
    (put : IndexWriter O E T X) (height : Nat) (parent : State O) (queued : List T)
    (error : X) (nonempty : queued ≠ [])
    (failed : walk put height empty queued = .error error)
    (retryPut : IndexWriter O E T X) (retryExclusive : Bool) (retryHeight : Option Nat) :
    let interrupted := flush put true true (some height) parent queued
    let retried := flush retryPut true retryExclusive retryHeight interrupted.parent interrupted.queued
    retried = unchanged parent [] ∧ retried.queued ≠ queued := by
  dsimp only
  rw [index_failure_discards_child_and_consumes_queue put height parent queued error nonempty failed]
  change flush retryPut true retryExclusive retryHeight parent [] = unchanged parent [] ∧
    (flush retryPut true retryExclusive retryHeight parent []).queued ≠ queued
  rw [empty_queue_shortcuts_all_fallible_calls]
  exact ⟨rfl, fun same => nonempty same.symm⟩

theorem successful_flush_applies_index_child_to_original_parent {O E T X : Type}
    (put : IndexWriter O E T X) (height : Nat) (parent : State O) (queued : List T)
    (child : Cache O E) (nonempty : queued ≠ [])
    (success : walk put height empty queued = .ok child) :
    flush put true true (some height) parent queued =
      ⟨applyCache parent child, [], child.events, none⟩ := by
  rw [post_take_dispatch put height parent queued nonempty, success]

end ShielddSecurity.TransferDeferredQueueSourceModel01

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.Failure
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.Failure

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.Outcome
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.Outcome

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.IndexWriter
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.IndexWriter

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.walk
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.walk

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.unchanged
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.unchanged

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.refused
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.refused

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.nonempty_test
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.nonempty_test

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.flush
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.flush

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.other_mode_preserves_queue
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.other_mode_preserves_queue

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.empty_queue_shortcuts_all_fallible_calls
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.empty_queue_shortcuts_all_fallible_calls

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.exclusive_failure_precedes_take
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.exclusive_failure_precedes_take

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.height_failure_precedes_take
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.height_failure_precedes_take

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.post_take_dispatch
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.post_take_dispatch

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.index_failure_discards_child_and_consumes_queue
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.index_failure_discards_child_and_consumes_queue

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.index_failure_preserves_preexisting_effect_state
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.index_failure_preserves_preexisting_effect_state

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.same_instance_retry_cannot_recreate_consumed_queue
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.same_instance_retry_cannot_recreate_consumed_queue

set_option pp.all true in
#check @ShielddSecurity.TransferDeferredQueueSourceModel01.successful_flush_applies_index_child_to_original_parent
#print axioms ShielddSecurity.TransferDeferredQueueSourceModel01.successful_flush_applies_index_child_to_original_parent
