import ShielddSecurity.TransferRawStateProgram01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferRawDeliveryComposition01

open TransferStateDelta TransferRawStateProgram01

/-! Success composition for the same raw program and existing delivery model.
The actual successful raw cache is recovered from the error-discarding adapter,
not supplied as a desired parent poststate. Deferred and PerTx indexing derive
their height/index facts, final cache, events and queue result from run success.
Concrete Rust/codec/primitive-cache and publication refinement remain external. -/

theorem asCache_some_iff {O E X : Type} (outcome : Outcome O E X) (cache : Cache O E) :
    asCache outcome = some cache ↔ outcome = ⟨cache, .ok ()⟩ := by
  cases outcome with
  | mk value result =>
    cases result with
    | error error => simp [asCache]
    | ok returnedUnit => cases returnedUnit; simp [asCache]

theorem prepareIndex_executionApi {O E T A X : Type} (api : Api O E T)
    (steps : State O → Step O E A X) (commands : List A) (mode : IndexMode)
    (transaction : T) (child : Delta O E) :
    prepareIndex (executionApi api steps commands) mode transaction child =
      prepareIndex api mode transaction child := by
  cases mode <;> rfl

theorem successful_raw_delivery_order {O E T A X : Type} (api : Api O E T)
    (steps : State O → Step O E A X) (commands : List A)
    (registryMatches exclusive : Bool) (mode : IndexMode) (transaction : T)
    (parent : State O) (queued : List T) (committed : Commit O E T)
    (success : run (executionApi api steps commands) registryMatches exclusive mode
      transaction parent queued = some committed) :
    registryMatches = true ∧ exclusive = true ∧
      ∃ cache prepared,
        walk (steps parent) empty commands = ⟨cache, .ok ()⟩ ∧
        prepareIndex api mode transaction ⟨parent, cache⟩ = some prepared ∧
        committed.parent = applyCache parent prepared.1.cache ∧
        committed.events = prepared.1.cache.events ∧
        committed.deferred = queued ++ prepared.2.toList := by
  obtain ⟨registry, unique, cache, prepared, performed, indexed, applied, events, deferred⟩ :=
    successful_delivery_order (executionApi api steps commands) registryMatches exclusive mode
      transaction parent queued committed success
  have raw : walk (steps parent) empty commands = ⟨cache, .ok ()⟩ := by
    apply (asCache_some_iff _ _).mp
    change asCache (walk (steps parent) empty commands) = some cache at performed
    exact performed
  rw [prepareIndex_executionApi] at indexed
  have original := index_preparation_preserves_parent api mode transaction ⟨parent, cache⟩ prepared indexed
  rw [original] at applied
  exact ⟨registry, unique, cache, prepared, raw, indexed, applied, events, deferred⟩

theorem successful_raw_deferred_exact {O E T A X : Type} (api : Api O E T)
    (steps : State O → Step O E A X) (commands : List A)
    (registryMatches exclusive : Bool) (transaction : T)
    (parent : State O) (queued : List T) (committed : Commit O E T)
    (success : run (executionApi api steps commands) registryMatches exclusive .deferred
      transaction parent queued = some committed) :
    registryMatches = true ∧ exclusive = true ∧
      ∃ cache height,
        walk (steps parent) empty commands = ⟨cache, .ok ()⟩ ∧
        api.height ⟨parent, cache⟩ = some height ∧
        committed.parent = applyCache parent cache ∧
        committed.events = cache.events ∧ committed.deferred = queued ++ [transaction] := by
  obtain ⟨registry, unique, cache, prepared, raw, indexed, applied, events, deferred⟩ :=
    successful_raw_delivery_order api steps commands registryMatches exclusive .deferred
      transaction parent queued committed success
  cases observed : api.height ⟨parent, cache⟩ with
  | none => simp [prepareIndex, observed] at indexed
  | some height =>
    have same : ((⟨parent, cache⟩ : Delta O E), some transaction) = prepared :=
      Option.some.inj (by simpa only [prepareIndex, observed, Option.map_some] using indexed)
    subst prepared
    exact ⟨registry, unique, cache, height, raw, observed, applied, events,
      by simpa only [Option.toList_some] using deferred⟩

theorem successful_raw_per_transaction_exact {O E T A X : Type} (api : Api O E T)
    (steps : State O → Step O E A X) (commands : List A)
    (registryMatches exclusive : Bool) (transaction : T)
    (parent : State O) (queued : List T) (committed : Commit O E T)
    (success : run (executionApi api steps commands) registryMatches exclusive .perTransaction
      transaction parent queued = some committed) :
    registryMatches = true ∧ exclusive = true ∧
      ∃ cache height indexedCache,
        walk (steps parent) empty commands = ⟨cache, .ok ()⟩ ∧
        api.height ⟨parent, cache⟩ = some height ∧
        api.index height transaction ⟨parent, cache⟩ = some indexedCache ∧
        committed.parent = applyCache parent indexedCache ∧
        committed.events = indexedCache.events ∧ committed.deferred = queued := by
  obtain ⟨registry, unique, cache, prepared, raw, indexed, applied, events, deferred⟩ :=
    successful_raw_delivery_order api steps commands registryMatches exclusive .perTransaction
      transaction parent queued committed success
  cases observed : api.height ⟨parent, cache⟩ with
  | none => simp [prepareIndex, observed] at indexed
  | some height =>
    cases written : api.index height transaction ⟨parent, cache⟩ with
    | none => simp [prepareIndex, observed, written] at indexed
    | some indexedCache =>
      have same : ((⟨parent, indexedCache⟩ : Delta O E), none) = prepared :=
        Option.some.inj (by simpa only [prepareIndex, observed, written,
          Option.bind_some, Option.map_some] using indexed)
      subst prepared
      exact ⟨registry, unique, cache, height, indexedCache, raw, observed, written, applied, events,
        by simpa only [Option.toList_none, List.append_nil] using deferred⟩

set_option pp.all true in
#check @asCache_some_iff
#print axioms asCache_some_iff
set_option pp.all true in
#check @prepareIndex_executionApi
#print axioms prepareIndex_executionApi
set_option pp.all true in
#check @successful_raw_delivery_order
#print axioms successful_raw_delivery_order
set_option pp.all true in
#check @successful_raw_deferred_exact
#print axioms successful_raw_deferred_exact
set_option pp.all true in
#check @successful_raw_per_transaction_exact
#print axioms successful_raw_per_transaction_exact

end ShielddSecurity.TransferRawDeliveryComposition01
