import ShielddSecurity.TransferCapabilityRows01
import ShielddSecurity.TransferEnvelopeSourceBridge

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferCapabilityEnvelope01
open TransferAcceptance TransferProofAdmissionModel TransferEnvelopeSourceBridge

/-! Verification provenance and constructive slot validation compose to exact
retained-envelope, local relation, family and singleton statement association.
Origin records success of the individual or separately fresh-randomized batch
program. It does not turn batch success into per-item cryptographic knowledge.
The native byte decoder, trusted-key identity, Rust extraction/container meaning,
cryptographic verification and Transfer row/semantic interpretation remain open.
No assumed BoundRows or desired item/coverage/claim equation is used. -/

def Origin (decode : List Nat → Option ClaimContext) (registry : Registry)
    (capability : Capability) : Prop :=
  (∃ item verified, verifyEncodedIndividual decode registry item verified = some capability) ∨
  (∃ items verified capabilities,
    verifyEncodedBatch decode registry items verified = some capabilities ∧ capability ∈ capabilities)

theorem individual_origin (decode : List Nat → Option ClaimContext) (registry : Registry)
    (item : Item) (verified : Bool) (capability : Capability)
    (success : verifyEncodedIndividual decode registry item verified = some capability) :
    Origin decode registry capability := Or.inl ⟨item, verified, success⟩

theorem batch_origin (decode : List Nat → Option ClaimContext) (registry : Registry)
    (items : List Item) (verified : Bool) (capabilities : List Capability) (capability : Capability)
    (success : verifyEncodedBatch decode registry items verified = some capabilities)
    (inside : capability ∈ capabilities) : Origin decode registry capability :=
  Or.inr ⟨items, verified, capabilities, success, inside⟩

theorem origin_bound (decode : List Nat → Option ClaimContext) (registry : Registry)
    (capability : Capability) (origin : Origin decode registry capability) :
    ∃ claim relation, decode capability.item.envelope = some claim ∧
      registry.relation capability.item.family = some relation ∧
      ClaimBound capability.item.family relation capability.item.statement claim ∧
      capability.registry = registry.identity := by
  rcases origin with ⟨item, verified, success⟩ | ⟨items, verified, capabilities, success, inside⟩
  · obtain ⟨claim, relation, decoded, lookup, bound, _, registered, sameItem⟩ :=
      individual_envelope_join decode registry item verified capability success
    refine ⟨claim, relation, ?_, ?_, ?_, registered⟩
    · rw [sameItem]
      exact decoded
    · rw [sameItem]
      exact lookup
    · rw [sameItem]
      exact bound
  · obtain ⟨first, rest, relation, _, sourceOrder, fromEnvelope, lookup,
      contexts, _, sameItems, registered⟩ :=
      batch_envelope_join decode registry items verified capabilities success
    have itemPresent : capability.item ∈ capabilities.map Capability.item :=
      List.mem_map.mpr ⟨capability, inside, rfl⟩
    have entryPresent : capability.item ∈ (first :: rest).map Entry.item := by
      rw [sourceOrder, ← sameItems]
      exact itemPresent
    obtain ⟨entry, present, sameItem⟩ := List.mem_map.mp entryPresent
    have context := contexts entry present
    refine ⟨entry.claim, relation, ?_, ?_, ?_, registered capability inside⟩
    · rw [← sameItem]
      exact fromEnvelope entry present
    · rw [← sameItem, context.1]
      exact lookup
    · rw [← sameItem, context.1]
      exact context.2

theorem input_family_checked (slots : List Nat) (expected : Nat → Item) (families : Nat → Nat)
    (registry : Nat) (rows result : List (Nat × Capability))
    (success : TransferCapabilityRows01.validate slots expected families registry rows = some result) :
    ∀ row ∈ rows, row.2.item.family = families row.1 := by
  have inserted := (TransferCapabilityRows01.validation_success slots expected families registry rows result success).1
  have retained : result.Perm rows := by
    simpa only [List.append_nil] using
      (TransferCapabilityRows01.collect_success rows [] result
        (by simp [TransferCapabilityRows01.keys]) inserted).2
  intro row inside
  exact TransferCapabilityRows01.every_result_family_checked slots expected families registry
    rows result success row (retained.mem_iff.mpr inside)

theorem location_family_mismatch_rejected (slots : List Nat) (expected : Nat → Item)
    (families : Nat → Nat) (registry slot : Nat) (rows : List (Nat × Capability))
    (present : slot ∈ slots) (wrong : (expected slot).family ≠ families slot) :
    ¬ ∃ result, TransferCapabilityRows01.validate slots expected families registry rows = some result := by
  rintro ⟨result, success⟩
  obtain ⟨capability, inside, _, sameItem⟩ :=
    TransferCapabilityRows01.every_expected_slot_checked slots expected families registry rows result success slot present
  have family := input_family_checked slots expected families registry rows result success
    (slot, capability) inside
  rw [sameItem] at family
  exact wrong family

theorem constructor_envelope_join (decode : List Nat → Option ClaimContext) (registry : Registry)
    (slots : List Nat) (expected : Nat → Item) (families : Nat → Nat)
    (rows result : List (Nat × Capability))
    (success : TransferCapabilityRows01.validate slots expected families registry.identity rows = some result)
    (origins : ∀ row ∈ rows, Origin decode registry row.2) :
    ∀ slot ∈ slots, ∃ claim relation, decode (expected slot).envelope = some claim ∧
      registry.relation (families slot) = some relation ∧
      ClaimBound (families slot) relation (expected slot).statement claim := by
  intro slot present
  obtain ⟨capability, inside, _, sameItem⟩ := TransferCapabilityRows01.every_expected_slot_checked
    slots expected families registry.identity rows result success slot present
  have family := input_family_checked slots expected families registry.identity rows result success
    (slot, capability) inside
  obtain ⟨claim, relation, decoded, lookup, bound, _⟩ :=
    origin_bound decode registry capability (origins (slot, capability) inside)
  rw [sameItem] at decoded lookup bound family
  rw [family] at lookup bound
  exact ⟨claim, relation, decoded, lookup, bound⟩

end ShielddSecurity.TransferCapabilityEnvelope01

set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityEnvelope01.Origin
#print axioms ShielddSecurity.TransferCapabilityEnvelope01.Origin
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityEnvelope01.individual_origin
#print axioms ShielddSecurity.TransferCapabilityEnvelope01.individual_origin
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityEnvelope01.batch_origin
#print axioms ShielddSecurity.TransferCapabilityEnvelope01.batch_origin
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityEnvelope01.origin_bound
#print axioms ShielddSecurity.TransferCapabilityEnvelope01.origin_bound
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityEnvelope01.input_family_checked
#print axioms ShielddSecurity.TransferCapabilityEnvelope01.input_family_checked
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityEnvelope01.location_family_mismatch_rejected
#print axioms ShielddSecurity.TransferCapabilityEnvelope01.location_family_mismatch_rejected
set_option pp.all true in
#check @ShielddSecurity.TransferCapabilityEnvelope01.constructor_envelope_join
#print axioms ShielddSecurity.TransferCapabilityEnvelope01.constructor_envelope_join
