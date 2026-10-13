import ShielddSecurity.TransferStateDelta

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferRawStateProgram01

open TransferStateDelta

/-! A failure-aware child-cache program. A raw callback may return an error
after changing its child cache. The arbitrary list recurrence retains that
cache and suppresses the remaining callbacks. Only the enclosing delivery
adapter discards an error result before parent apply and queue append.

This models mutable error propagation and callback ordering, not Rust aliasing,
Clone, primitive storage behavior, proof validity, or durable publication.
The existing late-delivery failure controls exercise enclosing child discard;
the additional delayed-token raw-volume control remains unexecuted. -/

structure Outcome (O E X : Type) where
  cache : Cache O E
  result : Except X Unit

abbrev Step (O E A X : Type) := Cache O E → A → Outcome O E X

def next {O E X : Type} (earlier : Outcome O E X)
    (later : Cache O E → Outcome O E X) : Outcome O E X :=
  match earlier.result with
  | .error error => ⟨earlier.cache, .error error⟩
  | .ok () => later earlier.cache

def walk {O E A X : Type} (step : Step O E A X) :
    Cache O E → List A → Outcome O E X
  | cache, [] => ⟨cache, .ok ()⟩
  | cache, command :: rest => next (step cache command) (fun updated => walk step updated rest)

theorem next_associative {O E X : Type} (first : Outcome O E X)
    (second third : Cache O E → Outcome O E X) :
    next (next first second) third = next first (fun cache => next (second cache) third) := by
  cases first with
  | mk cache result =>
    cases result with
    | error error => rfl
    | ok returnedUnit => cases returnedUnit; rfl

theorem walk_append {O E A X : Type} (step : Step O E A X)
    (cache : Cache O E) (earlierCommands suffix : List A) :
    walk step cache (earlierCommands ++ suffix) =
      next (walk step cache earlierCommands) (fun updated => walk step updated suffix) := by
  induction earlierCommands generalizing cache with
  | nil => rfl
  | cons command rest ih =>
    simp only [List.cons_append, walk]
    rw [next_associative]
    congr 1
    funext updated
    exact ih updated

theorem error_stops_suffix {O E A X : Type} (step : Step O E A X)
    (initial failureCache : Cache O E) (earlierCommands suffix : List A) (error : X)
    (failed : walk step initial earlierCommands = ⟨failureCache, .error error⟩) :
    walk step initial (earlierCommands ++ suffix) = ⟨failureCache, .error error⟩ := by
  rw [walk_append, failed]
  rfl

theorem successful_prefix_dispatch {O E A X : Type} (step : Step O E A X)
    (initial middle : Cache O E) (earlierCommands suffix : List A)
    (passed : walk step initial earlierCommands = ⟨middle, .ok ()⟩) :
    walk step initial (earlierCommands ++ suffix) = walk step middle suffix := by
  rw [walk_append, passed]
  rfl

theorem prefix_then_failure_retains_failure_cache {O E A X : Type}
    (step : Step O E A X) (initial middle failureCache : Cache O E)
    (earlierCommands suffix : List A) (command : A) (error : X)
    (passed : walk step initial earlierCommands = ⟨middle, .ok ()⟩)
    (failed : step middle command = ⟨failureCache, .error error⟩) :
    walk step initial (earlierCommands ++ command :: suffix) = ⟨failureCache, .error error⟩ := by
  rw [successful_prefix_dispatch step initial middle earlierCommands (command :: suffix) passed]
  simp only [walk, failed, next]

theorem prefix_then_readonly_rejection_keeps_prefix_cache {O E A X : Type}
    (step : Step O E A X) (initial middle : Cache O E)
    (earlierCommands suffix : List A) (command : A) (error : X)
    (passed : walk step initial earlierCommands = ⟨middle, .ok ()⟩)
    (failed : step middle command = ⟨middle, .error error⟩) :
    walk step initial (earlierCommands ++ command :: suffix) = ⟨middle, .error error⟩ :=
  prefix_then_failure_retains_failure_cache step initial middle middle earlierCommands suffix command error passed failed

def asCache {O E X : Type} (outcome : Outcome O E X) : Option (Cache O E) :=
  match outcome.result with
  | .error _ => none
  | .ok () => some outcome.cache

theorem asCache_error {O E X : Type} (failureCache : Cache O E) (error : X) :
    asCache (⟨failureCache, .error error⟩ : Outcome O E X) = none := rfl

theorem asCache_success {O E X : Type} (cache : Cache O E) :
    asCache (⟨cache, .ok ()⟩ : Outcome O E X) = some cache := rfl

def executionApi {O E T A X : Type} (api : Api O E T)
    (steps : State O → Step O E A X) (commands : List A) : Api O E T :=
  {api with execute := fun child => asCache (walk (steps child.parent) child.cache commands)}

theorem raw_error_rejects_delivery {O E T A X : Type}
    (api : Api O E T) (steps : State O → Step O E A X) (commands : List A)
    (registryMatches exclusive : Bool) (mode : IndexMode) (transaction : T)
    (parent : State O) (queued : List T) (failureCache : Cache O E) (error : X)
    (failed : walk (steps parent) empty commands = ⟨failureCache, .error error⟩) :
    run (executionApi api steps commands) registryMatches exclusive mode transaction parent queued = none := by
  cases registryMatches with
  | false => rfl
  | true =>
    cases exclusive with
    | false => rfl
    | true => simp only [run, begin, executionApi, ↓reduceIte, Option.bind_some, failed, asCache,
        Option.bind_none]

theorem raw_error_preserves_parent_and_queue {O E T A X : Type}
    (api : Api O E T) (steps : State O → Step O E A X) (commands : List A)
    (registryMatches exclusive : Bool) (mode : IndexMode) (transaction : T)
    (parent : State O) (queued : List T) (failureCache : Cache O E) (error : X)
    (failed : walk (steps parent) empty commands = ⟨failureCache, .error error⟩) :
    finish parent queued
      (run (executionApi api steps commands) registryMatches exclusive mode transaction parent queued) =
        (parent, queued) := by
  exact delivery_failure_preserves_parent_and_queue _ _ _ _ _ _ _
    (raw_error_rejects_delivery api steps commands registryMatches exclusive mode transaction parent queued failureCache error failed)

set_option pp.all true in
#check @Outcome
#print axioms Outcome
set_option pp.all true in
#check @Step
#print axioms Step
set_option pp.all true in
#check @next
#print axioms next
set_option pp.all true in
#check @walk
#print axioms walk
set_option pp.all true in
#check @next_associative
#print axioms next_associative
set_option pp.all true in
#check @walk_append
#print axioms walk_append
set_option pp.all true in
#check @error_stops_suffix
#print axioms error_stops_suffix
set_option pp.all true in
#check @successful_prefix_dispatch
#print axioms successful_prefix_dispatch
set_option pp.all true in
#check @prefix_then_failure_retains_failure_cache
#print axioms prefix_then_failure_retains_failure_cache
set_option pp.all true in
#check @prefix_then_readonly_rejection_keeps_prefix_cache
#print axioms prefix_then_readonly_rejection_keeps_prefix_cache
set_option pp.all true in
#check @asCache
#print axioms asCache
set_option pp.all true in
#check @asCache_error
#print axioms asCache_error
set_option pp.all true in
#check @asCache_success
#print axioms asCache_success
set_option pp.all true in
#check @executionApi
#print axioms executionApi
set_option pp.all true in
#check @raw_error_rejects_delivery
#print axioms raw_error_rejects_delivery
set_option pp.all true in
#check @raw_error_preserves_parent_and_queue
#print axioms raw_error_preserves_parent_and_queue

end ShielddSecurity.TransferRawStateProgram01
