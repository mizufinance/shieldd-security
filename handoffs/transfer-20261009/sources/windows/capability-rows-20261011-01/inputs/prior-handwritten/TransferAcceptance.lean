import Init.Data.List.Perm

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferAcceptance

/-- Family, statement and canonical envelope identity checked by ensure_binds.
Registry identity is separately established by the transaction artifact caller. -/
structure Item where
  family : Nat
  statement : Nat
  envelope : List Nat
  deriving DecidableEq

structure Capability where
  registry : Nat
  item : Item

/-- Projection of Envelope.check_context. Values stand for canonical decoded
bytes; decoding, source refinement and Pari knowledge remain separate contracts. -/
structure ClaimContext where
  family : Nat
  relation : Nat
  publicInputs : List Nat
  commitments : List Nat

def ClaimBound (family relation statement : Nat) (claim : ClaimContext) : Prop :=
  claim.family = family ∧ claim.relation = relation ∧
    claim.publicInputs = [statement] ∧ claim.commitments.length = 1

theorem wrong_family_fails_closed (family relation statement : Nat) (claim : ClaimContext)
    (wrong : claim.family ≠ family) : ¬ ClaimBound family relation statement claim := by
  intro bound
  exact wrong bound.1

theorem wrong_relation_fails_closed (family relation statement : Nat) (claim : ClaimContext)
    (wrong : claim.relation ≠ relation) : ¬ ClaimBound family relation statement claim := by
  intro bound
  exact wrong bound.2.1

theorem exact_public_and_committed_shape (family relation statement : Nat) (claim : ClaimContext)
    (bound : ClaimBound family relation statement claim) :
    claim.publicInputs = [statement] ∧ claim.commitments.length = 1 := by
  exact bound.2.2

/-- Registry.verify_items rejects an empty batch or a family mismatch before
calling the envelope batch verifier and before minting capabilities. -/
def FamilyBatch (family : Nat) (items : List Item) : Prop :=
  items ≠ [] ∧ ∀ item ∈ items, item.family = family

theorem empty_batch_fails_closed (family : Nat) : ¬ FamilyBatch family [] := by
  intro bound
  exact bound.1 rfl

theorem mixed_family_batch_fails_closed (family : Nat) (items : List Item) (item : Item)
    (inside : item ∈ items) (wrong : item.family ≠ family) : ¬ FamilyBatch family items := by
  intro bound
  exact wrong (bound.2 item inside)

/-- Digest-level transaction effect frame: parameters, optional memo/default,
optional fee-funding/default, action count, then ordered action digests. The
concrete digest widths, little-endian count, nested hashes and byte/proto source
refinement remain separate; none is asserted injective here. -/
structure EffectFrame where
  parameters : Nat
  memo : Nat
  feeFunding : Nat
  actions : List Nat

def effectFields (frame : EffectFrame) : List Nat :=
  frame.parameters :: frame.memo :: frame.feeFunding :: frame.actions.length :: frame.actions

theorem effect_frame_injective : ∀ first second : EffectFrame,
    effectFields first = effectFields second → first = second := by
  intro first second same
  cases first with
  | mk p m f actions =>
      cases second with
      | mk p' m' f' actions' =>
          simp only [effectFields, List.cons.injEq] at same
          rcases same with ⟨hp, hm, hf, _, ha⟩
          subst p'
          subst m'
          subst f'
          subst actions'
          rfl

/-- Equal top-level hashes of different digest frames exhibit a collision.
Equal frames with different underlying actions require the separate nested
hash/encoding analysis; no signature or hash injectivity premise is used. -/
theorem effect_equivocation_exposes_collision (hash : List Nat → Nat)
    (first second : EffectFrame) (different : first ≠ second)
    (same : hash (effectFields first) = hash (effectFields second)) :
    effectFields first ≠ effectFields second ∧
      hash (effectFields first) = hash (effectFields second) := by
  exact ⟨fun fields => different (effect_frame_injective first second fields), same⟩

/-- The witness anchor is independently bound to transaction context. It is
excluded from the action effect preimage, so signature-message binding alone
does not supply either of these equalities. -/
def AnchorBound (bodyAnchor contextAnchor publicAnchor : Nat) : Prop :=
  bodyAnchor = contextAnchor ∧ publicAnchor = contextAnchor

theorem independent_anchor_join (bodyAnchor contextAnchor publicAnchor : Nat)
    (bound : AnchorBound bodyAnchor contextAnchor publicAnchor) : bodyAnchor = publicAnchor := by
  exact bound.1.trans bound.2.symm

theorem wrong_body_anchor_fails_closed (bodyAnchor contextAnchor publicAnchor : Nat)
    (wrong : bodyAnchor ≠ contextAnchor) : ¬ AnchorBound bodyAnchor contextAnchor publicAnchor := by
  intro bound
  exact wrong bound.1

/-- Native admission reserves an identity aggregate key for transactions with
no shielded proofs and the canonical no-binding sentinel. Circuit-legal zero
action blindings do not bypass this independent transaction rule. -/
def BindingMode (proofCount : Nat) (identityKey canonicalSentinel signatureValid : Bool) : Prop :=
  if identityKey then proofCount = 0 ∧ canonicalSentinel = true else signatureValid = true

theorem proof_bearing_binding_nonidentity (proofCount : Nat)
    (identityKey canonicalSentinel signatureValid : Bool) (positive : 0 < proofCount)
    (accepted : BindingMode proofCount identityKey canonicalSentinel signatureValid) :
    identityKey = false := by
  cases identityKey with
  | false => rfl
  | true =>
      have zero : proofCount = 0 := accepted.1
      exact False.elim (Nat.ne_of_gt positive zero)

theorem identity_requires_canonical_sentinel (proofCount : Nat)
    (canonicalSentinel signatureValid : Bool)
    (accepted : BindingMode proofCount true canonicalSentinel signatureValid) :
    proofCount = 0 ∧ canonicalSentinel = true := by
  exact accepted

/-- Input rows may carry identical capability bytes in different slots. The
actual constructor rejects duplicate slot keys and checks exact slot coverage. -/
structure BoundRows (expectedSlots : List Nat) (expected : Nat → Item)
    (rows : List (Nat × Capability)) (registry : Nat) : Prop where
  uniqueSlots : (rows.map Prod.fst).Nodup
  exactCoverage : (rows.map Prod.fst).Perm expectedSlots
  binds : ∀ row ∈ rows, row.2.registry = registry ∧ row.2.item = expected row.1

theorem every_expected_slot_bound (slots : List Nat) (expected : Nat → Item)
    (rows : List (Nat × Capability)) (registry : Nat)
    (bound : BoundRows slots expected rows registry) :
    ∀ slot ∈ slots, ∃ capability, (slot, capability) ∈ rows ∧
      capability.registry = registry ∧ capability.item = expected slot := by
  intro slot present
  have member : slot ∈ rows.map Prod.fst := bound.exactCoverage.mem_iff.mpr present
  obtain ⟨row, inside, same⟩ := List.mem_map.mp member
  obtain ⟨actualSlot, capability⟩ := row
  simp only [Prod.fst] at same
  subst actualSlot
  exact ⟨capability, inside, bound.binds _ inside⟩

theorem duplicate_slot_fails_closed (slots : List Nat) (expected : Nat → Item)
    (registry slot : Nat) (first second : Capability) (rest : List (Nat × Capability)) :
    ¬ BoundRows slots expected ((slot, first) :: (slot, second) :: rest) registry := by
  intro bound
  have unique := bound.uniqueSlots
  simp at unique

theorem wrong_registry_fails_closed (slots : List Nat) (expected : Nat → Item)
    (rows : List (Nat × Capability)) (registry : Nat) (row : Nat × Capability)
    (inside : row ∈ rows) (wrong : row.2.registry ≠ registry) :
    ¬ BoundRows slots expected rows registry := by
  intro bound
  exact wrong (bound.binds row inside).1

theorem wrong_slot_item_fails_closed (slots : List Nat) (expected : Nat → Item)
    (rows : List (Nat × Capability)) (registry : Nat) (row : Nat × Capability)
    (inside : row ∈ rows) (wrong : row.2.item ≠ expected row.1) :
    ¬ BoundRows slots expected rows registry := by
  intro bound
  exact wrong (bound.binds row inside).2

/-- A valid upstream proof contract may be instantiated only after matching
keys/setup/parameters/relations and all Transfer semantic joins are discharged.
This theorem proves transaction slot coverage and application composition. -/
theorem expected_slots_satisfy_contract (slots : List Nat) (expected : Nat → Item)
    (rows : List (Nat × Capability)) (registry : Nat) (contract : Item → Prop)
    (bound : BoundRows slots expected rows registry)
    (verifiedContract : ∀ row ∈ rows, row.2.registry = registry → contract row.2.item) :
    ∀ slot ∈ slots, contract (expected slot) := by
  intro slot present
  obtain ⟨capability, inside, registered, item⟩ :=
    every_expected_slot_bound slots expected rows registry bound slot present
  rw [← item]
  exact verifiedContract _ inside registered

/-- Delivery checks the transaction artifact registry, so caller composition
supplies the registry premise that individual ensure_binds does not supply. -/
theorem delivery_registry_join (rows : List (Nat × Capability))
    (artifactRegistry activeRegistry : Nat)
    (artifact : ∀ row ∈ rows, row.2.registry = artifactRegistry)
    (delivery : artifactRegistry = activeRegistry) :
    ∀ row ∈ rows, row.2.registry = activeRegistry := by
  intro row present
  exact (artifact row present).trans delivery

/-- Transaction-lookup-hash-collision-independent cache reuse: both complete raw bytes and registry ID
are compared after the hash lookup. No hash injectivity premise is needed.
Registry-ID binding to the actual trusted key set is a separate cryptographic
application contract. Historical/admission state is rechecked at delivery; it is not cached here. -/
theorem exact_cache_reuse (storedRaw requestedRaw : List Nat)
    (storedRegistry activeRegistry : Nat) (statelessValid : List Nat → Nat → Prop)
    (stored : statelessValid storedRaw storedRegistry)
    (rawEquality : storedRaw = requestedRaw)
    (registryEquality : storedRegistry = activeRegistry) :
    statelessValid requestedRaw activeRegistry := by
  simpa [← rawEquality, ← registryEquality] using stored

set_option pp.all true in
#check @proof_bearing_binding_nonidentity
#print axioms proof_bearing_binding_nonidentity
set_option pp.all true in
#check @identity_requires_canonical_sentinel
#print axioms identity_requires_canonical_sentinel
set_option pp.all true in
#check @effect_frame_injective
#print axioms effect_frame_injective
set_option pp.all true in
#check @effect_equivocation_exposes_collision
#print axioms effect_equivocation_exposes_collision
set_option pp.all true in
#check @independent_anchor_join
#print axioms independent_anchor_join
set_option pp.all true in
#check @wrong_body_anchor_fails_closed
#print axioms wrong_body_anchor_fails_closed
set_option pp.all true in
#check @wrong_family_fails_closed
#print axioms wrong_family_fails_closed
set_option pp.all true in
#check @wrong_relation_fails_closed
#print axioms wrong_relation_fails_closed
set_option pp.all true in
#check @exact_public_and_committed_shape
#print axioms exact_public_and_committed_shape
set_option pp.all true in
#check @empty_batch_fails_closed
#print axioms empty_batch_fails_closed
set_option pp.all true in
#check @mixed_family_batch_fails_closed
#print axioms mixed_family_batch_fails_closed
set_option pp.all true in
#check @wrong_registry_fails_closed
#print axioms wrong_registry_fails_closed
set_option pp.all true in
#check @wrong_slot_item_fails_closed
#print axioms wrong_slot_item_fails_closed
set_option pp.all true in
#check @duplicate_slot_fails_closed
#print axioms duplicate_slot_fails_closed
set_option pp.all true in
#check @every_expected_slot_bound
#print axioms every_expected_slot_bound
set_option pp.all true in
#check @expected_slots_satisfy_contract
#print axioms expected_slots_satisfy_contract
set_option pp.all true in
#check @delivery_registry_join
#print axioms delivery_registry_join
set_option pp.all true in
#check @exact_cache_reuse
#print axioms exact_cache_reuse

end ShielddSecurity.TransferAcceptance
