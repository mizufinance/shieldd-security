import ShielddSecurity.TransferNullifierStaging

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferNullifierPublicCall

open TransferNullifierStaging

/-! The public `nullify_all` wrapper checks emptiness before requiring a
transaction source ID, then invokes normal staging with durable checks enabled.
This is a functional source-correspondence target; decoding, authenticated
storage reads and Rust persistent-container ownership remain separate. -/

inductive PublicFailure where
  | missingSource
  | staging (reason : TransferNullifierStaging.Failure)
  deriving DecidableEq

def nullifyAll (usizeMax : Nat) (before : Block) (request : List Nat)
    (hasTransactionSource : Bool)
    (read : Except TransferNullifierStaging.Failure (Nat → Bool)) :
    Except PublicFailure Block :=
  if request = [] then .ok before
  else if hasTransactionSource then
    match stage usizeMax before request true read with
    | .error reason => .error (.staging reason)
    | .ok after => .ok after
  else .error .missingSource

theorem empty_returns_before (usizeMax : Nat) (before : Block)
    (hasTransactionSource : Bool)
    (read : Except TransferNullifierStaging.Failure (Nat → Bool)) :
    nullifyAll usizeMax before [] hasTransactionSource read = .ok before := by
  simp [nullifyAll]

theorem nonempty_without_source_refused (usizeMax : Nat) (before : Block)
    (request : List Nat) (read : Except TransferNullifierStaging.Failure (Nat → Bool))
    (nonempty : request ≠ []) :
    nullifyAll usizeMax before request false read = .error .missingSource := by
  simp [nullifyAll, nonempty]

theorem staging_failure_propagated (usizeMax : Nat) (before : Block)
    (request : List Nat) (read : Except TransferNullifierStaging.Failure (Nat → Bool))
    (reason : TransferNullifierStaging.Failure) (nonempty : request ≠ [])
    (failed : stage usizeMax before request true read = .error reason) :
    nullifyAll usizeMax before request true read = .error (.staging reason) := by
  simp [nullifyAll, nonempty, failed]

theorem nonempty_success_requires_source (usizeMax : Nat) (before after : Block)
    (request : List Nat) (hasTransactionSource : Bool)
    (read : Except TransferNullifierStaging.Failure (Nat → Bool))
    (nonempty : request ≠ [])
    (success : nullifyAll usizeMax before request hasTransactionSource read = .ok after) :
    hasTransactionSource = true := by
  cases hasTransactionSource with
  | false => simp [nullifyAll, nonempty] at success
  | true => rfl

theorem nonempty_success_is_append (usizeMax : Nat) (before after : Block)
    (request : List Nat) (hasTransactionSource : Bool)
    (read : Except TransferNullifierStaging.Failure (Nat → Bool))
    (nonempty : request ≠ [])
    (success : nullifyAll usizeMax before request hasTransactionSource read = .ok after) :
    after = append before request := by
  have source := nonempty_success_requires_source usizeMax before after request
    hasTransactionSource read nonempty success
  cases staged : stage usizeMax before request true read with
  | error reason => simp [nullifyAll, nonempty, source, staged] at success
  | ok middle =>
      have same : middle = after := by
        simpa [nullifyAll, nonempty, source, staged] using success
      exact same.symm.trans (successful_stage_is_append usizeMax before request true read middle staged)

theorem successful_nonempty_order (usizeMax : Nat) (before after : Block)
    (request : List Nat) (hasTransactionSource : Bool)
    (read : Except TransferNullifierStaging.Failure (Nat → Bool))
    (nonempty : request ≠ [])
    (success : nullifyAll usizeMax before request hasTransactionSource read = .ok after) :
    after.ordered = before.ordered ++ request := by
  rw [nonempty_success_is_append usizeMax before after request hasTransactionSource read nonempty success]
  rfl

theorem successful_nonempty_consumes_every_identity (usizeMax : Nat) (before after : Block)
    (request : List Nat) (hasTransactionSource : Bool)
    (read : Except TransferNullifierStaging.Failure (Nat → Bool))
    (nonempty : request ≠ [])
    (success : nullifyAll usizeMax before request hasTransactionSource read = .ok after)
    (nullifier : Nat) (inside : nullifier ∈ request) :
    after.membership nullifier = true := by
  rw [nonempty_success_is_append usizeMax before after request hasTransactionSource read nonempty success]
  exact (append_membership before request nullifier).2 (Or.inr inside)

theorem successful_nonempty_frames_other_identity (usizeMax : Nat) (before after : Block)
    (request : List Nat) (hasTransactionSource : Bool)
    (read : Except TransferNullifierStaging.Failure (Nat → Bool))
    (nonempty : request ≠ [])
    (success : nullifyAll usizeMax before request hasTransactionSource read = .ok after)
    (nullifier : Nat) (outside : nullifier ∉ request) :
    after.membership nullifier = before.membership nullifier := by
  rw [nonempty_success_is_append usizeMax before after request hasTransactionSource read nonempty success]
  exact append_frames_other_identity before request nullifier outside

theorem successful_nonempty_retains_pending (usizeMax : Nat) (before after : Block)
    (request : List Nat) (hasTransactionSource : Bool)
    (read : Except TransferNullifierStaging.Failure (Nat → Bool))
    (nonempty : request ≠ [])
    (success : nullifyAll usizeMax before request hasTransactionSource read = .ok after)
    (nullifier : Nat) (alreadyPending : before.membership nullifier = true) :
    after.membership nullifier = true := by
  rw [nonempty_success_is_append usizeMax before after request hasTransactionSource read nonempty success]
  exact (append_membership before request nullifier).2 (Or.inl alreadyPending)

/-- The body and fee call the wrapper separately with both serialized slots.
There is no amount, optional-dummy, zero-identity or private-padding filter.
Normal staging still rejects duplicate identities and prior pending conflicts. -/
theorem body_and_fee_calls_consume_four_slots (usizeMax : Nat) (before middle after : Block)
    (body0 body1 fee0 fee1 : Nat) (bodySource feeSource : Bool)
    (bodyRead feeRead : Except TransferNullifierStaging.Failure (Nat → Bool))
    (bodySuccess : nullifyAll usizeMax before [body0, body1] bodySource bodyRead = .ok middle)
    (feeSuccess : nullifyAll usizeMax middle [fee0, fee1] feeSource feeRead = .ok after) :
    after.membership body0 = true ∧ after.membership body1 = true ∧
    after.membership fee0 = true ∧ after.membership fee1 = true := by
  have bodyConsumed := successful_nonempty_consumes_every_identity usizeMax before middle
    [body0, body1] bodySource bodyRead (by simp) bodySuccess
  have retained := successful_nonempty_retains_pending usizeMax middle after
    [fee0, fee1] feeSource feeRead (by simp) feeSuccess
  have feeConsumed := successful_nonempty_consumes_every_identity usizeMax middle after
    [fee0, fee1] feeSource feeRead (by simp) feeSuccess
  exact ⟨retained body0 (bodyConsumed body0 (by simp)),
    retained body1 (bodyConsumed body1 (by simp)),
    feeConsumed fee0 (by simp), feeConsumed fee1 (by simp)⟩

set_option pp.all true in
#check @empty_returns_before
#print axioms empty_returns_before
set_option pp.all true in
#check @nonempty_without_source_refused
#print axioms nonempty_without_source_refused
set_option pp.all true in
#check @staging_failure_propagated
#print axioms staging_failure_propagated
set_option pp.all true in
#check @nonempty_success_requires_source
#print axioms nonempty_success_requires_source
set_option pp.all true in
#check @nonempty_success_is_append
#print axioms nonempty_success_is_append
set_option pp.all true in
#check @successful_nonempty_order
#print axioms successful_nonempty_order
set_option pp.all true in
#check @successful_nonempty_consumes_every_identity
#print axioms successful_nonempty_consumes_every_identity
set_option pp.all true in
#check @successful_nonempty_frames_other_identity
#print axioms successful_nonempty_frames_other_identity
set_option pp.all true in
#check @successful_nonempty_retains_pending
#print axioms successful_nonempty_retains_pending
set_option pp.all true in
#check @body_and_fee_calls_consume_four_slots
#print axioms body_and_fee_calls_consume_four_slots

end ShielddSecurity.TransferNullifierPublicCall
