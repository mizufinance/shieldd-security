import ShielddSecurity.TransferRawStateProgram01
import ShielddSecurity.TransferNullifierReaderVector01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferNullifierBatchSource01

open TransferStateDelta TransferRawStateProgram01 TransferNullifierReaderVector01

/-! Source-order public nullify_all / stage_nullifiers(check_durable=true) model.
Nonempty input requires a transaction source. Duplicate, sealed, saturating
capacity, pending and authenticated-vector checks precede one object_put.
Pending/getter/codec/alias correspondence is explicit. This primitive retains
its input cache on error; the cache can already contain earlier raw effects.
It does not promise rollback of a whole raw handler or durable publication. -/

structure Pending where
  ordered : List Nat
  membership : Nat → Bool
  sealed : Bool

inductive BatchError where
  | source | duplicate | sealed | capacity | pending | reader | spent

structure Backend (O E : Type) where
  pending : Delta O E → Pending
  readerGate : Delta O E → Bool
  lookup : Delta O E → Nat → Option Bool
  encode : Pending → O

def uniqueLoop : List Nat → List Nat → Bool
  | _, [] => true
  | seen, key :: rest => if seen.contains key then false else uniqueLoop (key :: seen) rest

def appendPending (previous : Pending) (keys : List Nat) : Pending :=
  ⟨previous.ordered ++ keys, fun key => previous.membership key || keys.contains key, false⟩

def inspect {O E : Type} (backend : Backend O E) (wordMax capacity : Nat)
    (child : Delta O E) (keys : List Nat) : Except BatchError Pending :=
  if uniqueLoop [] keys then
    let previous := backend.pending child
    if previous.sealed then .error .sealed
    else if Nat.min (previous.ordered.length + keys.length) wordMax ≤ capacity then
      if keys.all (fun key => !previous.membership key) then
        match contains (backend.readerGate child) (backend.lookup child) previous.membership keys with
        | none => .error .reader
        | some flags =>
          if zipUnspent keys flags then .ok (appendPending previous keys) else .error .spent
      else .error .pending
    else .error .capacity
  else .error .duplicate

def executeNullify {O E : Type} (backend : Backend O E) (wordMax capacity objectKey : Nat)
    (sourceHasId : Bool) (child : Delta O E) (keys : List Nat) : Outcome O E BatchError :=
  if keys.isEmpty then ⟨child.cache, .ok ()⟩
  else if sourceHasId then
    match inspect backend wordMax capacity child keys with
    | .error error => ⟨child.cache, .error error⟩
    | .ok next => ⟨(putObject child objectKey (some (backend.encode next))).cache, .ok ()⟩
  else ⟨child.cache, .error .source⟩

theorem saturating_capacity_exact (current requested wordMax capacity : Nat)
    (belowWord : capacity < wordMax)
    (allowed : Nat.min (current + requested) wordMax ≤ capacity) :
    current + requested ≤ capacity := by
  rw [Nat.min_eq_min] at allowed
  by_cases withinWord : current + requested ≤ wordMax
  · rw [Nat.min_eq_left withinWord] at allowed
    exact allowed
  · have wordBelow := Nat.le_of_lt (Nat.lt_of_not_ge withinWord)
    rw [Nat.min_eq_right wordBelow] at allowed
    exact False.elim ((Nat.not_le_of_gt belowWord) allowed)

theorem duplicate_pair_refused (key : Nat) (rest : List Nat) :
    uniqueLoop [] (key :: key :: rest) = false := by
  simp [uniqueLoop]

theorem inspection_success_order {O E : Type} (backend : Backend O E)
    (wordMax capacity : Nat) (child : Delta O E) (keys : List Nat) (next : Pending)
    (success : inspect backend wordMax capacity child keys = .ok next) :
    ∃ previous flags,
      previous = backend.pending child ∧ uniqueLoop [] keys = true ∧ previous.sealed = false ∧
      Nat.min (previous.ordered.length + keys.length) wordMax ≤ capacity ∧
      keys.all (fun key => !previous.membership key) = true ∧
      contains (backend.readerGate child) (backend.lookup child) previous.membership keys = some flags ∧
      zipUnspent keys flags = true ∧ next = appendPending previous keys := by
  cases unique : uniqueLoop [] keys with
  | false => simp [inspect, unique] at success
  | true =>
    cases sealed : (backend.pending child).sealed with
    | true => simp [inspect, unique, sealed] at success
    | false =>
      by_cases allowed : Nat.min ((backend.pending child).ordered.length + keys.length) wordMax ≤ capacity
      · cases fresh : keys.all (fun key => !(backend.pending child).membership key) with
        | false => simp [inspect, unique, sealed, allowed, fresh] at success
        | true =>
          cases observed : contains (backend.readerGate child) (backend.lookup child)
              (backend.pending child).membership keys with
          | none => simp [inspect, unique, sealed, allowed, fresh, observed] at success
          | some flags =>
            cases unspent : zipUnspent keys flags with
            | false => simp [inspect, unique, sealed, allowed, fresh, observed, unspent] at success
            | true =>
              have same : appendPending (backend.pending child) keys = next := by
                simpa [inspect, unique, sealed, allowed, fresh, observed, unspent] using success
              exact ⟨backend.pending child, flags, rfl, rfl, sealed, allowed, fresh, observed,
                unspent, same.symm⟩
      · simp [inspect, unique, sealed, allowed] at success

theorem inspection_success_capacity_and_all_inputs {O E : Type} (backend : Backend O E)
    (wordMax capacity : Nat) (child : Delta O E) (keys : List Nat) (next : Pending)
    (belowWord : capacity < wordMax)
    (success : inspect backend wordMax capacity child keys = .ok next) :
    next.ordered = (backend.pending child).ordered ++ keys ∧
      next.ordered.length ≤ capacity ∧ next.sealed = false ∧
      ∀ key ∈ keys, backend.lookup child key = some false ∧
        (backend.pending child).membership key = false ∧ next.membership key = true := by
  obtain ⟨previous, flags, observedPending, _, _, allowed, _, observedReader, unspent, same⟩ :=
    inspection_success_order backend wordMax capacity child keys next success
  subst previous
  obtain ⟨_, allInputs⟩ := contains_success_unspent (backend.readerGate child)
    (backend.lookup child) (backend.pending child).membership keys flags observedReader unspent
  rw [same]
  refine ⟨rfl, ?_, rfl, ?_⟩
  · change ((backend.pending child).ordered ++ keys).length ≤ capacity
    rw [List.length_append]
    exact saturating_capacity_exact _ _ wordMax capacity belowWord allowed
  · intro key inside
    obtain ⟨durableFalse, pendingFalse⟩ := allInputs key inside
    refine ⟨durableFalse, pendingFalse, ?_⟩
    change ((backend.pending child).membership key || keys.contains key) = true
    simp [inside]

theorem empty_batch_skips_source_and_reads {O E : Type} (backend : Backend O E)
    (wordMax capacity objectKey : Nat) (sourceHasId : Bool) (child : Delta O E) :
    executeNullify backend wordMax capacity objectKey sourceHasId child [] =
      ⟨child.cache, .ok ()⟩ := rfl

theorem nontransaction_source_refused {O E : Type} (backend : Backend O E)
    (wordMax capacity objectKey : Nat) (child : Delta O E) (keys : List Nat)
    (nonempty : keys.isEmpty = false) :
    executeNullify backend wordMax capacity objectKey false child keys =
      ⟨child.cache, .error .source⟩ := by
  simp [executeNullify, nonempty]

theorem stage_failure_retains_input_cache {O E : Type} (backend : Backend O E)
    (wordMax capacity objectKey : Nat) (child : Delta O E) (keys : List Nat)
    (nonempty : keys.isEmpty = false) (error : BatchError)
    (rejected : inspect backend wordMax capacity child keys = .error error) :
    executeNullify backend wordMax capacity objectKey true child keys =
      ⟨child.cache, .error error⟩ := by
  simp [executeNullify, nonempty, rejected]

theorem successful_nonempty_batch_single_object_write {O E : Type} (backend : Backend O E)
    (wordMax capacity objectKey : Nat) (sourceHasId : Bool) (child : Delta O E)
    (keys : List Nat) (cache : Cache O E) (nonempty : keys.isEmpty = false)
    (success : executeNullify backend wordMax capacity objectKey sourceHasId child keys =
      ⟨cache, .ok ()⟩) :
    sourceHasId = true ∧ ∃ next,
      inspect backend wordMax capacity child keys = .ok next ∧
      cache = (putObject child objectKey (some (backend.encode next))).cache := by
  cases sourceHasId with
  | false => simp [executeNullify, nonempty] at success
  | true =>
    cases observed : inspect backend wordMax capacity child keys with
    | error error => simp [executeNullify, nonempty, observed] at success
    | ok next =>
      have same : (putObject child objectKey (some (backend.encode next))).cache = cache := by
        simpa [executeNullify, nonempty, observed] using success
      exact ⟨rfl, next, rfl, same.symm⟩

theorem successful_batch_frames_other_components {O E : Type} (backend : Backend O E)
    (wordMax capacity objectKey : Nat) (sourceHasId : Bool) (child : Delta O E)
    (keys : List Nat) (cache : Cache O E) (nonempty : keys.isEmpty = false)
    (success : executeNullify backend wordMax capacity objectKey sourceHasId child keys =
      ⟨cache, .ok ()⟩) :
    cache.verifiable = child.cache.verifiable ∧ cache.nonverifiable = child.cache.nonverifiable ∧
      cache.events = child.cache.events ∧
      ∀ other, other ≠ objectKey → cache.objects other = child.cache.objects other := by
  obtain ⟨_, next, _, same⟩ := successful_nonempty_batch_single_object_write
    backend wordMax capacity objectKey sourceHasId child keys cache nonempty success
  rw [same]
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro other different
  simp only [putObject, if_neg different]

set_option pp.all true in
#check @Pending
#print axioms Pending
set_option pp.all true in
#check @BatchError
#print axioms BatchError
set_option pp.all true in
#check @Backend
#print axioms Backend
set_option pp.all true in
#check @uniqueLoop
#print axioms uniqueLoop
set_option pp.all true in
#check @appendPending
#print axioms appendPending
set_option pp.all true in
#check @inspect
#print axioms inspect
set_option pp.all true in
#check @executeNullify
#print axioms executeNullify
set_option pp.all true in
#check @saturating_capacity_exact
#print axioms saturating_capacity_exact
set_option pp.all true in
#check @duplicate_pair_refused
#print axioms duplicate_pair_refused
set_option pp.all true in
#check @inspection_success_order
#print axioms inspection_success_order
set_option pp.all true in
#check @inspection_success_capacity_and_all_inputs
#print axioms inspection_success_capacity_and_all_inputs
set_option pp.all true in
#check @empty_batch_skips_source_and_reads
#print axioms empty_batch_skips_source_and_reads
set_option pp.all true in
#check @nontransaction_source_refused
#print axioms nontransaction_source_refused
set_option pp.all true in
#check @stage_failure_retains_input_cache
#print axioms stage_failure_retains_input_cache
set_option pp.all true in
#check @successful_nonempty_batch_single_object_write
#print axioms successful_nonempty_batch_single_object_write
set_option pp.all true in
#check @successful_batch_frames_other_components
#print axioms successful_batch_frames_other_components

end ShielddSecurity.TransferNullifierBatchSource01
