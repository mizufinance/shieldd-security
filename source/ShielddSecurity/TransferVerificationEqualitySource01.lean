import ShielddSecurity.TransferCapabilitySource01

set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferVerificationEqualitySource01

open TransferStateDelta TransferRawStateProgram01

/-! Source-level Verification::eq and Verified::ensure_binds. The statement
field denotes the scalar value already present in Verification. Equality of
that scalar does not establish semantic correspondence or equality of source
statement preimages. Envelope denotes to_bytes output; actual serializer,
scalar representation, decoded statement/proof semantics and verified-token
provenance remain interfaces. ensure_binds does not inspect registry_id. -/

structure Item where
  family : Nat
  statement : Nat
  envelope : List Nat
  deriving DecidableEq

structure Verified where
  registry : Nat
  item : Item

def itemEq (left right : Item) : Bool :=
  (left.family == right.family) && (left.statement == right.statement) &&
    (left.envelope == right.envelope)

def ensureBinds (requestedFamily : Nat) (verified : Verified) (candidate : Item) : Bool :=
  (requestedFamily == verified.item.family) && itemEq verified.item candidate

theorem itemEq_iff_eq (left right : Item) : itemEq left right = true ↔ left = right := by
  cases left
  cases right
  simp [itemEq, and_assoc]

theorem binding_success_recovers_every_compared_field (requestedFamily : Nat)
    (verified : Verified) (candidate : Item) (passed : ensureBinds requestedFamily verified candidate = true) :
    requestedFamily = verified.item.family ∧ verified.item.family = candidate.family ∧
      verified.item.statement = candidate.statement ∧ verified.item.envelope = candidate.envelope := by
  simpa [ensureBinds, itemEq, and_assoc] using passed

theorem registry_identity_is_not_checked_here (requestedFamily firstRegistry secondRegistry : Nat)
    (verifiedItem candidate : Item) :
    ensureBinds requestedFamily ⟨firstRegistry, verifiedItem⟩ candidate =
      ensureBinds requestedFamily ⟨secondRegistry, verifiedItem⟩ candidate := rfl

theorem requested_family_mismatch_refused (requestedFamily : Nat) (verified : Verified) (candidate : Item)
    (different : requestedFamily ≠ verified.item.family) :
    ensureBinds requestedFamily verified candidate = false := by
  simp [ensureBinds, different]

theorem candidate_family_mismatch_refused (requestedFamily : Nat) (verified : Verified) (candidate : Item)
    (different : verified.item.family ≠ candidate.family) :
    ensureBinds requestedFamily verified candidate = false := by
  simp [ensureBinds, itemEq, different]

theorem statement_scalar_mismatch_refused (requestedFamily : Nat) (verified : Verified) (candidate : Item)
    (different : verified.item.statement ≠ candidate.statement) :
    ensureBinds requestedFamily verified candidate = false := by
  simp [ensureBinds, itemEq, different]

theorem serialized_envelope_mismatch_refused (requestedFamily : Nat) (verified : Verified) (candidate : Item)
    (different : verified.item.envelope ≠ candidate.envelope) :
    ensureBinds requestedFamily verified candidate = false := by
  simp [ensureBinds, itemEq, different]

theorem fieldwise_exact_rebinding_dispatches_raw_action {O E K X A : Type}
    (raw : TransferRawEffectsSource01.Backend O E X)
    (extract : A → TransferCapabilitySource01.ProofContext → Except K Item) (inputs outputs : A → List Nat)
    (wordMax capacity pendingKey entryKey dayKey : Nat) (action : A)
    (token : TransferCapabilitySource01.Validated Item) (child : Delta O E) (current : Item)
    (observed : extract action token.context = .ok current) (matched : itemEq current token.item = true) :
    TransferCapabilitySource01.execute raw extract inputs outputs wordMax capacity pendingKey entryKey dayKey action token child =
      TransferCapabilitySource01.liftRaw
        (TransferRawEffectsSource01.executeTransfer raw wordMax capacity pendingKey entryKey dayKey
          true (TransferCapabilitySource01.isOrdinary token.context) child (inputs action) (outputs action)) := by
  have same := (itemEq_iff_eq current token.item).mp matched
  rw [same] at observed
  exact TransferCapabilitySource01.exact_rebinding_dispatches_projected_action raw extract inputs outputs
    wordMax capacity pendingKey entryKey dayKey action token child observed

set_option pp.all true in
#check @Item
#print axioms Item
set_option pp.all true in
#check @Verified
#print axioms Verified
set_option pp.all true in
#check @itemEq
#print axioms itemEq
set_option pp.all true in
#check @ensureBinds
#print axioms ensureBinds
set_option pp.all true in
#check @itemEq_iff_eq
#print axioms itemEq_iff_eq
set_option pp.all true in
#check @binding_success_recovers_every_compared_field
#print axioms binding_success_recovers_every_compared_field
set_option pp.all true in
#check @registry_identity_is_not_checked_here
#print axioms registry_identity_is_not_checked_here
set_option pp.all true in
#check @requested_family_mismatch_refused
#print axioms requested_family_mismatch_refused
set_option pp.all true in
#check @candidate_family_mismatch_refused
#print axioms candidate_family_mismatch_refused
set_option pp.all true in
#check @statement_scalar_mismatch_refused
#print axioms statement_scalar_mismatch_refused
set_option pp.all true in
#check @serialized_envelope_mismatch_refused
#print axioms serialized_envelope_mismatch_refused
set_option pp.all true in
#check @fieldwise_exact_rebinding_dispatches_raw_action
#print axioms fieldwise_exact_rebinding_dispatches_raw_action

set_option pp.all true in
#check @instDecidableEqItem
#print axioms instDecidableEqItem

end ShielddSecurity.TransferVerificationEqualitySource01
