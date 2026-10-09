import ShielddSecurity.TransferTransaction

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferIndexing

open TransferAdmission TransferTransaction

/-!
Independent executable model of App's three index modes. Successful delivery
applies a Transfer effect delta before adding a DeferredBatch queue entry; its
index is written later by a separate savepoint. NoIndex records neither list.

The exact pinned flush drains its queue before fallible index writes. This model
keeps that behavior visible instead of supplying failure rollback as a premise.
Duplicate transaction identities provide a concrete fallible write here; native
codec, count overflow and store faults are additional source contracts. A native
Host end-block flush error panics, and consumer abort/rollback/retry discipline,
actual Rust state transaction drop, durable writer and published queries remain
separate obligations. These are model consequences, not a Rust refinement or
evidence that an application consumer retries a failed end block.
-/

inductive Mode where
  | noIndex | perTx | deferredBatch
  deriving DecidableEq

structure State where
  effects : EffectState
  deferred : List Nat

def recordIndex (mode : Mode) (state : State) (transaction : Nat) : State :=
  match mode with
  | .noIndex => state
  | .perTx => { state with effects :=
      { state.effects with transactionIndex := state.effects.transactionIndex ++ [transaction] } }
  | .deferredBatch => { state with deferred := state.deferred ++ [transaction] }

def runTransaction (mode : Mode) (state : State) (entries : List RoutedSlot)
    (transaction : Nat) : Option State :=
  (runRoutedSlots state.effects entries).map fun after =>
    recordIndex mode { state with effects := after } transaction

theorem record_no_index (state : State) (transaction : Nat) :
    recordIndex .noIndex state transaction = state := rfl

theorem record_per_tx (state : State) (transaction : Nat) :
    (recordIndex .perTx state transaction).effects.transactionIndex =
      state.effects.transactionIndex ++ [transaction] ∧
    (recordIndex .perTx state transaction).deferred = state.deferred := ⟨rfl, rfl⟩

theorem record_deferred (state : State) (transaction : Nat) :
    (recordIndex .deferredBatch state transaction).effects = state.effects ∧
    (recordIndex .deferredBatch state transaction).deferred = state.deferred ++ [transaction] := ⟨rfl, rfl⟩

theorem mode_transaction_success (mode : Mode) (state after : State)
    (entries : List RoutedSlot) (transaction : Nat)
    (success : runTransaction mode state entries transaction = some after) :
    after = recordIndex mode
      { state with effects := applyRoutedSlots state.effects entries } transaction := by
  cases result : runRoutedSlots state.effects entries with
  | none => simp [runTransaction, result] at success
  | some middle =>
      have exactEffects := routed_slots_success_exact state.effects middle entries result
      have exactState : recordIndex mode { state with effects := middle } transaction = after :=
        Option.some.inj (by simpa [runTransaction, result] using success)
      simpa [exactEffects] using exactState.symm

/-- Each current index write rejects an already indexed transaction identity. -/
def runIndexWrites (indexed : List Nat) : List Nat → Option (List Nat)
  | [] => some indexed
  | transaction :: rest =>
      if transaction ∈ indexed then none
      else runIndexWrites (indexed ++ [transaction]) rest

theorem index_writes_success_exact (indexed transactions after : List Nat)
    (success : runIndexWrites indexed transactions = some after) :
    after = indexed ++ transactions := by
  induction transactions generalizing indexed with
  | nil => simpa [runIndexWrites] using (Option.some.inj success).symm
  | cons transaction rest ih =>
      by_cases duplicate : transaction ∈ indexed
      · simp [runIndexWrites, duplicate] at success
      · have tailSuccess : runIndexWrites (indexed ++ [transaction]) rest = some after := by
          simpa [runIndexWrites, duplicate] using success
        simpa [List.append_assoc] using ih (indexed ++ [transaction]) tailSuccess

/-- Outcome carries the remaining pending state even on failure. The source
drains before the separate index savepoint; a failed savepoint is not applied. -/
def flushDeferred (state : State) : State × Bool :=
  let drained := { state with deferred := [] }
  match runIndexWrites state.effects.transactionIndex state.deferred with
  | none => (drained, false)
  | some indexed =>
      ({ drained with effects := { drained.effects with transactionIndex := indexed } }, true)

theorem flush_success_index (state : State) (success : (flushDeferred state).2 = true) :
    (flushDeferred state).1.effects.transactionIndex =
      state.effects.transactionIndex ++ state.deferred ∧
    (flushDeferred state).1.deferred = [] := by
  cases result : runIndexWrites state.effects.transactionIndex state.deferred with
  | none => simp [flushDeferred, result] at success
  | some indexed =>
      have exactIndex := index_writes_success_exact _ _ _ result
      simp [flushDeferred, result, exactIndex]

theorem flush_failure_preserves_effects_and_drains (state : State)
    (failure : (flushDeferred state).2 = false) :
    (flushDeferred state).1.effects = state.effects ∧
    (flushDeferred state).1.deferred = [] := by
  cases result : runIndexWrites state.effects.transactionIndex state.deferred with
  | none => simp [flushDeferred, result]
  | some indexed => simp [flushDeferred, result] at failure

theorem drained_flush_is_empty_retry (state : State) :
    flushDeferred { state with deferred := [] } = ({ state with deferred := [] }, true) := by
  simp [flushDeferred, runIndexWrites]

set_option pp.all true in
#check @record_no_index
#print axioms record_no_index
set_option pp.all true in
#check @record_per_tx
#print axioms record_per_tx
set_option pp.all true in
#check @record_deferred
#print axioms record_deferred
set_option pp.all true in
#check @mode_transaction_success
#print axioms mode_transaction_success
set_option pp.all true in
#check @index_writes_success_exact
#print axioms index_writes_success_exact
set_option pp.all true in
#check @flush_success_index
#print axioms flush_success_index
set_option pp.all true in
#check @flush_failure_preserves_effects_and_drains
#print axioms flush_failure_preserves_effects_and_drains
set_option pp.all true in
#check @drained_flush_is_empty_retry
#print axioms drained_flush_is_empty_retry

end ShielddSecurity.TransferIndexing
