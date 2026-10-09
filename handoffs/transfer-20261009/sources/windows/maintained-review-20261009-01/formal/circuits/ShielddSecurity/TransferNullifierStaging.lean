import Lean

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferNullifierStaging

/-! Functional model of the normal pinned `stage_nullifiers` path. Nullifiers
are arbitrary numeric identities, including padding slots. The persistent
vector/set clone and cnidarium object-write correspondence are separate Rust
obligations. This model neither publishes the durable tree nor interprets a
failed read as an unspent result. -/

def blockLimit : Nat := 32768

structure Block where
  sealed : Bool
  ordered : List Nat
  membership : Nat → Bool

inductive Failure where
  | duplicate | sealed | capacity | pending | reader | durable
  deriving DecidableEq

def fresh (request : List Nat) : Bool := decide request.Nodup

def absent (membership : Nat → Bool) (request : List Nat) : Bool :=
  request.all fun nullifier => !(membership nullifier)

def append (block : Block) (request : List Nat) : Block :=
  ⟨false, block.ordered ++ request,
    fun nullifier => block.membership nullifier || request.contains nullifier⟩

/-- The durable read returns one authenticated Boolean per requested identity.
The caller supplies an error or the resulting predicate, not a fabricated
all-unspent result. Saturation is represented explicitly. -/
def stage (usizeMax : Nat) (block : Block) (request : List Nat)
    (checkDurable : Bool) (read : Except Failure (Nat → Bool)) : Except Failure Block :=
  if fresh request then
    if block.sealed then .error .sealed
    else if min (block.ordered.length + request.length) usizeMax ≤ blockLimit then
      if absent block.membership request then
        if checkDurable then
          match read with
          | .error _ => .error .reader
          | .ok durable => if absent durable request then .ok (append block request)
            else .error .durable
        else .ok (append block request)
      else .error .pending
    else .error .capacity
  else .error .duplicate

theorem fresh_iff_nodup (request : List Nat) : fresh request = true ↔ request.Nodup := by
  simp only [fresh, decide_eq_true_eq]

theorem absent_iff (membership : Nat → Bool) (request : List Nat) :
    absent membership request = true ↔ ∀ nullifier ∈ request, membership nullifier = false := by
  simp [absent]

theorem append_order (block : Block) (request : List Nat) :
    (append block request).ordered = block.ordered ++ request := rfl

theorem append_membership (block : Block) (request : List Nat) (nullifier : Nat) :
    (append block request).membership nullifier = true ↔
      block.membership nullifier = true ∨ nullifier ∈ request := by
  simp [append]

theorem append_frames_other_identity (block : Block) (request : List Nat) (nullifier : Nat)
    (outside : nullifier ∉ request) :
    (append block request).membership nullifier = block.membership nullifier := by
  simp [append, outside]

theorem duplicates_refused (usizeMax : Nat) (block : Block) (request : List Nat)
    (checkDurable : Bool) (read : Except Failure (Nat → Bool))
    (duplicate : ¬request.Nodup) :
    stage usizeMax block request checkDurable read = .error .duplicate := by
  simp [stage, fresh, duplicate]

theorem sealed_refused (usizeMax : Nat) (block : Block) (request : List Nat)
    (checkDurable : Bool) (read : Except Failure (Nat → Bool))
    (unique : request.Nodup) (sealed : block.sealed = true) :
    stage usizeMax block request checkDurable read = .error .sealed := by
  simp [stage, fresh, unique, sealed]

theorem capacity_refused (usizeMax : Nat) (block : Block) (request : List Nat)
    (checkDurable : Bool) (read : Except Failure (Nat → Bool))
    (unique : request.Nodup) (isOpen : block.sealed = false)
    (over : ¬min (block.ordered.length + request.length) usizeMax ≤ blockLimit) :
    stage usizeMax block request checkDurable read = .error .capacity := by
  simp [stage, fresh, unique, isOpen, over]

theorem pending_refused (usizeMax : Nat) (block : Block) (request : List Nat)
    (checkDurable : Bool) (read : Except Failure (Nat → Bool))
    (unique : request.Nodup) (isOpen : block.sealed = false)
    (size : min (block.ordered.length + request.length) usizeMax ≤ blockLimit)
    (conflict : absent block.membership request = false) :
    stage usizeMax block request checkDurable read = .error .pending := by
  simp [stage, fresh, unique, isOpen, size, conflict]

theorem read_failure_refused (usizeMax : Nat) (block : Block) (request : List Nat)
    (failure : Failure) (unique : request.Nodup) (isOpen : block.sealed = false)
    (size : min (block.ordered.length + request.length) usizeMax ≤ blockLimit)
    (pending : absent block.membership request = true) :
    stage usizeMax block request true (.error failure) = .error .reader := by
  simp [stage, fresh, unique, isOpen, size, pending]

theorem durable_refused (usizeMax : Nat) (block : Block) (request : List Nat)
    (durable : Nat → Bool) (unique : request.Nodup) (isOpen : block.sealed = false)
    (size : min (block.ordered.length + request.length) usizeMax ≤ blockLimit)
    (pending : absent block.membership request = true)
    (spent : absent durable request = false) :
    stage usizeMax block request true (.ok durable) = .error .durable := by
  simp [stage, fresh, unique, isOpen, size, pending, spent]

theorem legal_request_appended (usizeMax : Nat) (block : Block) (request : List Nat)
    (durable : Nat → Bool) (unique : request.Nodup) (isOpen : block.sealed = false)
    (size : min (block.ordered.length + request.length) usizeMax ≤ blockLimit)
    (pending : absent block.membership request = true)
    (unspent : absent durable request = true) :
    stage usizeMax block request true (.ok durable) = .ok (append block request) := by
  simp [stage, fresh, unique, isOpen, size, pending, unspent]

/-- Trusted internal insertion may omit durable reads; it still checks local
duplicates, sealing, capacity and the pending membership set. -/
theorem internal_request_appended (usizeMax : Nat) (block : Block) (request : List Nat)
    (read : Except Failure (Nat → Bool)) (unique : request.Nodup) (isOpen : block.sealed = false)
    (size : min (block.ordered.length + request.length) usizeMax ≤ blockLimit)
    (pending : absent block.membership request = true) :
    stage usizeMax block request false read = .ok (append block request) := by
  simp [stage, fresh, unique, isOpen, size, pending]

theorem saturation_cannot_hide_overflow (usizeMax size : Nat)
    (platform : blockLimit < usizeMax) (accepted : min size usizeMax ≤ blockLimit) :
    size ≤ blockLimit := by
  by_cases unsaturated : size ≤ usizeMax
  · simpa only [Nat.min_eq_left unsaturated] using accepted
  · have capped : usizeMax ≤ blockLimit := by
      simpa only [Nat.min_eq_right (Nat.le_of_not_ge unsaturated)] using accepted
    exact False.elim (Nat.not_le_of_gt platform capped)

/-- Every successful branch returns the same complete ordered append. No
poststate equality is assumed as an input premise. -/
theorem successful_stage_is_append (usizeMax : Nat) (block : Block) (request : List Nat)
    (checkDurable : Bool) (read : Except Failure (Nat → Bool)) (after : Block)
    (success : stage usizeMax block request checkDurable read = .ok after) :
    after = append block request := by
  cases unique : fresh request with
  | false => simp [stage, unique] at success
  | true =>
    cases sealed : block.sealed with
    | true => simp [stage, unique, sealed] at success
    | false =>
      by_cases size : min (block.ordered.length + request.length) usizeMax ≤ blockLimit
      · cases pending : absent block.membership request with
        | false => simp [stage, unique, sealed, size, pending] at success
        | true =>
          cases checkDurable with
          | false => simpa [stage, unique, sealed, size, pending] using success.symm
          | true =>
            cases read with
            | error failure => simp [stage, unique, sealed, size, pending] at success
            | ok durable =>
              cases unspent : absent durable request with
              | false => simp [stage, unique, sealed, size, pending, unspent] at success
              | true => simpa [stage, unique, sealed, size, pending, unspent] using success.symm
      · simp [stage, unique, sealed, size] at success

def finish (before : Block) (result : Except Failure Block) : Block :=
  match result with
  | .error _ => before
  | .ok after => after

theorem failed_staging_preserves_block (before : Block) (failure : Failure) :
    finish before (.error failure) = before := rfl

set_option pp.all true in
#check @fresh_iff_nodup
#print axioms fresh_iff_nodup
set_option pp.all true in
#check @absent_iff
#print axioms absent_iff
set_option pp.all true in
#check @append_order
#print axioms append_order
set_option pp.all true in
#check @append_membership
#print axioms append_membership
set_option pp.all true in
#check @append_frames_other_identity
#print axioms append_frames_other_identity
set_option pp.all true in
#check @duplicates_refused
#print axioms duplicates_refused
set_option pp.all true in
#check @sealed_refused
#print axioms sealed_refused
set_option pp.all true in
#check @capacity_refused
#print axioms capacity_refused
set_option pp.all true in
#check @pending_refused
#print axioms pending_refused
set_option pp.all true in
#check @read_failure_refused
#print axioms read_failure_refused
set_option pp.all true in
#check @durable_refused
#print axioms durable_refused
set_option pp.all true in
#check @legal_request_appended
#print axioms legal_request_appended
set_option pp.all true in
#check @internal_request_appended
#print axioms internal_request_appended
set_option pp.all true in
#check @saturation_cannot_hide_overflow
#print axioms saturation_cannot_hide_overflow
set_option pp.all true in
#check @successful_stage_is_append
#print axioms successful_stage_is_append
set_option pp.all true in
#check @failed_staging_preserves_block
#print axioms failed_staging_preserves_block

end ShielddSecurity.TransferNullifierStaging
