import Lean

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferStateDelta

/-! Typed functional model of the pinned cnidarium child cache and Shieldd
delivery ordering. A cache entry distinguishes no write from a deletion.
Values denote immutable snapshots; correspondence for Clone/persistent object
containers and Rust ownership is a separate source obligation. This module
does not assume a desired poststate or assert durable-store publication. -/

abbrev Bytes := List Nat
abbrev View (V : Type) := Nat → Option V
abbrev Writes (V : Type) := Nat → Option (Option V)

def overlay {V : Type} (base : View V) (writes : Writes V) : View V :=
  fun key => match writes key with
    | none => base key
    | some value => value

def mergeWrites {V : Type} (older newer : Writes V) : Writes V :=
  fun key => match newer key with
    | none => older key
    | some value => some value

theorem overlay_merge {V : Type} (base : View V) (older newer : Writes V) :
    overlay base (mergeWrites older newer) = overlay (overlay base older) newer := by
  funext key
  cases selected : newer key <;> simp only [overlay, mergeWrites, selected]

structure State (O : Type) where
  verifiable : View Bytes
  nonverifiable : View Bytes
  objects : View O

structure Cache (O E : Type) where
  verifiable : Writes Bytes
  nonverifiable : Writes Bytes
  objects : Writes O
  events : List E

def empty {O E : Type} : Cache O E := ⟨fun _ => none, fun _ => none, fun _ => none, []⟩

def merge {O E : Type} (older newer : Cache O E) : Cache O E :=
  ⟨mergeWrites older.verifiable newer.verifiable,
   mergeWrites older.nonverifiable newer.nonverifiable,
   mergeWrites older.objects newer.objects, older.events ++ newer.events⟩

def applyCache {O E : Type} (base : State O) (cache : Cache O E) : State O :=
  ⟨overlay base.verifiable cache.verifiable,
   overlay base.nonverifiable cache.nonverifiable, overlay base.objects cache.objects⟩

theorem apply_empty {O E : Type} (base : State O) : applyCache base (empty (E := E)) = base := by
  cases base
  rfl

theorem apply_merge {O E : Type} (base : State O) (older newer : Cache O E) :
    applyCache base (merge older newer) = applyCache (applyCache base older) newer := by
  simp only [applyCache, merge, overlay_merge]

/-- The cache stack is folded from oldest to newest, ending with the leaf.
This symbolic recurrence matches flatten's merge order. -/
def flatten {O E : Type} : Cache O E → List (Cache O E) → Cache O E
  | accumulated, [] => accumulated
  | accumulated, layer :: rest => flatten (merge accumulated layer) rest

def applyLayers {O E : Type} : State O → List (Cache O E) → State O
  | base, [] => base
  | base, layer :: rest => applyLayers (applyCache base layer) rest

theorem flatten_applies_in_order {O E : Type} (base : State O)
    (layers : List (Cache O E)) (accumulated : Cache O E) :
    applyCache base (flatten accumulated layers) = applyLayers (applyCache base accumulated) layers := by
  induction layers generalizing accumulated with
  | nil => rfl
  | cons layer rest ih =>
      rw [flatten, ih, apply_merge]
      rfl

structure Delta (O E : Type) where
  parent : State O
  cache : Cache O E

def begin {O E : Type} (exclusive : Bool) (parent : State O) : Option (Delta O E) :=
  if exclusive then some ⟨parent, empty⟩ else none

def putObject {O E : Type} (delta : Delta O E) (key : Nat) (value : Option O) : Delta O E :=
  {delta with cache := {delta.cache with objects :=
    fun other => if other = key then some value else delta.cache.objects other}}

theorem object_write_preserves_parent {O E : Type} (delta : Delta O E) (key : Nat) (value : Option O) :
    (putObject delta key value).parent = delta.parent := rfl

theorem object_write_visible_in_child {O E : Type} (delta : Delta O E) (key : Nat) (value : Option O) :
    (applyCache (putObject delta key value).parent (putObject delta key value).cache).objects key = value := by
  simp only [putObject, applyCache, overlay, ite_true]

theorem object_write_frames_other_key {O E : Type} (delta : Delta O E) (key other : Nat)
    (value : Option O) (different : other ≠ key) :
    (applyCache (putObject delta key value).parent (putObject delta key value).cache).objects other =
      (applyCache delta.parent delta.cache).objects other := by
  simp only [putObject, applyCache, overlay, if_neg different]

theorem shared_parent_refused {O E : Type} (parent : State O) : begin (E := E) false parent = none := rfl

inductive IndexMode where
  | noIndex | perTransaction | deferred

structure Api (O E T : Type) where
  execute : Delta O E → Option (Cache O E)
  height : Delta O E → Option Nat
  index : Nat → T → Delta O E → Option (Cache O E)

def prepareIndex {O E T : Type} (api : Api O E T) (mode : IndexMode) (transaction : T)
    (delta : Delta O E) : Option (Delta O E × Option T) :=
  match mode with
  | .noIndex => some (delta, none)
  | .perTransaction => (api.height delta).bind fun height =>
      (api.index height transaction delta).map fun indexed => (⟨delta.parent, indexed⟩, none)
  | .deferred => (api.height delta).map fun _ => (delta, some transaction)

theorem index_preparation_preserves_parent {O E T : Type} (api : Api O E T)
    (mode : IndexMode) (transaction : T) (delta : Delta O E)
    (prepared : Delta O E × Option T)
    (success : prepareIndex api mode transaction delta = some prepared) :
    prepared.1.parent = delta.parent := by
  cases mode with
  | noIndex =>
      have same : (delta, none) = prepared := Option.some.inj success
      exact congrArg (fun pair : Delta O E × Option T => pair.1.parent) same.symm
  | perTransaction =>
      cases observed : api.height delta with
      | none => simp [prepareIndex, observed] at success
      | some height =>
          cases indexed : api.index height transaction delta with
          | none => simp [prepareIndex, observed, indexed] at success
          | some cache =>
              have same : ((⟨delta.parent, cache⟩ : Delta O E), none) = prepared :=
                Option.some.inj (by simpa only [prepareIndex, observed, indexed,
                  Option.bind_some, Option.map_some] using success)
              exact congrArg (fun pair : Delta O E × Option T => pair.1.parent) same.symm
  | deferred =>
      cases observed : api.height delta with
      | none => simp [prepareIndex, observed] at success
      | some height =>
          have same : (delta, some transaction) = prepared :=
            Option.some.inj (by simpa only [prepareIndex, observed, Option.map_some] using success)
          exact congrArg (fun pair : Delta O E × Option T => pair.1.parent) same.symm

structure Commit (O E T : Type) where
  parent : State O
  events : List E
  deferred : List T

/-- Registry check and exclusive begin precede effects. Index preparation
shares the child. Applying the cache precedes appending a deferred entry. -/
def run {O E T : Type} (api : Api O E T) (registryMatches exclusive : Bool)
    (mode : IndexMode) (transaction : T) (parent : State O) (queued : List T) : Option (Commit O E T) :=
  if registryMatches then
    (begin exclusive parent).bind fun child =>
      (api.execute child).bind fun executed =>
        (prepareIndex api mode transaction ⟨child.parent, executed⟩).map fun prepared =>
          ⟨applyCache prepared.1.parent prepared.1.cache, prepared.1.cache.events,
            queued ++ prepared.2.toList⟩
  else none

def finish {O E T : Type} (parent : State O) (queued : List T)
    (result : Option (Commit O E T)) : State O × List T :=
  match result with
  | none => (parent, queued)
  | some committed => (committed.parent, committed.deferred)

theorem delivery_failure_preserves_parent_and_queue {O E T : Type}
    (api : Api O E T) (registryMatches exclusive : Bool) (mode : IndexMode) (transaction : T)
    (parent : State O) (queued : List T)
    (failed : run api registryMatches exclusive mode transaction parent queued = none) :
    finish parent queued (run api registryMatches exclusive mode transaction parent queued) = (parent, queued) := by
  rw [failed]
  rfl

theorem successful_delivery_order {O E T : Type} (api : Api O E T)
    (registryMatches exclusive : Bool) (mode : IndexMode) (transaction : T)
    (parent : State O) (queued : List T) (committed : Commit O E T)
    (success : run api registryMatches exclusive mode transaction parent queued = some committed) :
    registryMatches = true ∧ exclusive = true ∧
      ∃ executed prepared,
        api.execute ⟨parent, empty⟩ = some executed ∧
        prepareIndex api mode transaction ⟨parent, executed⟩ = some prepared ∧
        committed.parent = applyCache prepared.1.parent prepared.1.cache ∧
        committed.events = prepared.1.cache.events ∧
        committed.deferred = queued ++ prepared.2.toList := by
  cases registryMatches with
  | false => simp [run] at success
  | true =>
    cases exclusive with
    | false => simp [run, begin] at success
    | true =>
      cases performed : api.execute ⟨parent, empty⟩ with
      | none => simp [run, begin, performed] at success
      | some executed =>
        cases indexed : prepareIndex api mode transaction ⟨parent, executed⟩ with
        | none => simp [run, begin, performed, indexed] at success
        | some prepared =>
          have same : (⟨applyCache prepared.1.parent prepared.1.cache, prepared.1.cache.events,
              queued ++ prepared.2.toList⟩ : Commit O E T) = committed :=
            Option.some.inj (by simpa only [run, begin, ↓reduceIte, Option.bind_some,
              performed, indexed, Option.map_some] using success)
          subst committed
          exact ⟨rfl, rfl, executed, prepared, rfl, indexed, rfl, rfl, rfl⟩

theorem successful_delivery_applies_child_to_original_parent {O E T : Type} (api : Api O E T)
    (registryMatches exclusive : Bool) (mode : IndexMode) (transaction : T)
    (parent : State O) (queued : List T) (committed : Commit O E T)
    (success : run api registryMatches exclusive mode transaction parent queued = some committed) :
    ∃ executed prepared,
      api.execute ⟨parent, empty⟩ = some executed ∧
      prepareIndex api mode transaction ⟨parent, executed⟩ = some prepared ∧
      committed.parent = applyCache parent prepared.1.cache ∧
      committed.deferred = queued ++ prepared.2.toList := by
  obtain ⟨_, _, executed, prepared, performed, indexed, applied, _, deferred⟩ :=
    successful_delivery_order api registryMatches exclusive mode transaction parent queued committed success
  have preserved := index_preparation_preserves_parent api mode transaction ⟨parent, executed⟩ prepared indexed
  rw [preserved] at applied
  exact ⟨executed, prepared, performed, indexed, applied, deferred⟩

set_option pp.all true in
#check @overlay_merge
#print axioms overlay_merge
set_option pp.all true in
#check @apply_empty
#print axioms apply_empty
set_option pp.all true in
#check @apply_merge
#print axioms apply_merge
set_option pp.all true in
#check @flatten_applies_in_order
#print axioms flatten_applies_in_order
set_option pp.all true in
#check @object_write_preserves_parent
#print axioms object_write_preserves_parent
set_option pp.all true in
#check @object_write_visible_in_child
#print axioms object_write_visible_in_child
set_option pp.all true in
#check @object_write_frames_other_key
#print axioms object_write_frames_other_key
set_option pp.all true in
#check @shared_parent_refused
#print axioms shared_parent_refused
set_option pp.all true in
#check @index_preparation_preserves_parent
#print axioms index_preparation_preserves_parent
set_option pp.all true in
#check @delivery_failure_preserves_parent_and_queue
#print axioms delivery_failure_preserves_parent_and_queue
set_option pp.all true in
#check @successful_delivery_order
#print axioms successful_delivery_order
set_option pp.all true in
#check @successful_delivery_applies_child_to_original_parent
#print axioms successful_delivery_applies_child_to_original_parent

end ShielddSecurity.TransferStateDelta
