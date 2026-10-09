import ShielddSecurity.TransferSem

set_option maxHeartbeats 200000

/-! Raw authorization construction under explicit group closure and computed
point legality. The sender commitment is rebuilt before compliance membership.
No AuthorizationSem conclusion or desired scalar/point output is an input. -/
namespace ShielddSecurity.TransferAuthorizationBranchCompletion

open TransferCore TransferSem

structure GroupClosure (c : Crypto) : Prop where
  generatorSubgroup : c.subgroup c.generator
  mulSubgroup : ∀ n p, c.subgroup p → c.subgroup (c.mul n p)
  addSubgroup : ∀ p q, c.subgroup p → c.subgroup q → c.subgroup (c.add p q)

structure RawInputs where
  ak : Affine
  nk : Nat
  randomizer : Nat

def incomingHash (c : Crypto) (i : RawInputs) : Nat :=
  c.hash .incomingViewingKey ([i.nk] ++ pointFields i.ak)

def computedIVK (c : Crypto) (i : RawInputs) : Nat := incomingHash c i % scalarOrder

def computedRK (c : Crypto) (i : RawInputs) : Affine :=
  c.add i.ak (c.mul i.randomizer c.generator)

structure LegalInputs (c : Crypto) (base : TransferSem.Witness) (i : RawInputs) : Prop where
  akValid : ValidPoint c i.ak
  akNonidentity : nonidentity i.ak
  nkCanonical : i.nk < fieldModulus
  randomizerBounded : i.randomizer < scalarOrder
  assetNonzero : base.asset ≠ 0
  ringNonidentity : nonidentity (ring c base)
  ivkNonzero : computedIVK c i ≠ 0
  owner : c.mul (computedIVK c i) base.sender.address.diversified = base.sender.address.transmission
  rnkDHNonidentity : nonidentity (c.mul (computedIVK c i) base.sender.rnkDH)
  rkNonidentity : nonidentity (computedRK c i)

def constructAuth (c : Crypto) (i : RawInputs) : Authorization :=
  ⟨i.ak, i.nk, computedIVK c i, incomingHash c i / scalarOrder, i.randomizer, computedRK c i⟩

def provisional (c : Crypto) (base : TransferSem.Witness) (i : RawInputs) : TransferSem.Witness :=
  {base with auth := constructAuth c i}

def senderCommitment (c : Crypto) (base : TransferSem.Witness) (i : RawInputs) : Nat :=
  if base.regulated then c.hash .regulatedNullifierCommitment [rnk c (provisional c base i)]
  else base.sender.rnkCommitment

def construct (c : Crypto) (base : TransferSem.Witness) (i : RawInputs) : TransferSem.Witness :=
  {provisional c base i with sender := {base.sender with rnkCommitment := senderCommitment c base i}}

theorem ivk_bounded (c : Crypto) (i : RawInputs) : computedIVK c i < scalarOrder :=
  Nat.mod_lt _ (by decide)

theorem quotient_bounded (c : Crypto) (i : RawInputs) (cryptoCanonical : CanonicalCrypto c) :
    incomingHash c i / scalarOrder ≤ 8 := by
  have bounded : incomingHash c i < fieldModulus := cryptoCanonical.1 _ _
  have division := Nat.mod_add_div (incomingHash c i) scalarOrder
  have remainder : incomingHash c i % scalarOrder < scalarOrder := Nat.mod_lt _ (by decide)
  unfold scalarOrder fieldModulus at *
  omega

theorem scalar_decomposition (c : Crypto) (i : RawInputs) :
    incomingHash c i = computedIVK c i + scalarOrder * (incomingHash c i / scalarOrder) := by
  exact (Nat.mod_add_div _ _).symm

theorem rk_valid (c : Crypto) (i : RawInputs) (akValid : ValidPoint c i.ak)
    (cryptoCanonical : CanonicalCrypto c) (group : GroupClosure c) : ValidPoint c (computedRK c i) :=
  ⟨cryptoCanonical.2.2.2.1 _ _,
    group.addSubgroup _ _ akValid.2 (group.mulSubgroup _ _ group.generatorSubgroup)⟩

theorem rnk_ignores_sender_commitment (c : Crypto) (base : TransferSem.Witness) (i : RawInputs) :
    rnk c (construct c base i) = rnk c (provisional c base i) := rfl

theorem constructed_authorization_semantics (c : Crypto) (base : TransferSem.Witness)
    (i : RawInputs) (legal : LegalInputs c base i) (cryptoCanonical : CanonicalCrypto c)
    (group : GroupClosure c) : AuthorizationSem c (construct c base i) := by
  refine ⟨legal.akValid, legal.akNonidentity, legal.assetNonzero, legal.ringNonidentity,
    ⟨ivk_bounded c i, legal.ivkNonzero, quotient_bounded c i cryptoCanonical, scalar_decomposition c i⟩,
    legal.owner, legal.rnkDHNonidentity, ?_, legal.randomizerBounded,
    rk_valid c i legal.akValid cryptoCanonical group, legal.rkNonidentity, rfl⟩
  intro regulated
  change base.regulated = true at regulated
  change c.hash .regulatedNullifierCommitment [rnk c (construct c base i)] = senderCommitment c base i
  simp only [senderCommitment, regulated, ↓reduceIte, rnk_ignores_sender_commitment]

theorem restore_full_record (c : Crypto) (base : TransferSem.Witness) (i : RawInputs) :
    { construct c base i with auth := base.auth, sender :=
        { (construct c base i).sender with rnkCommitment := base.sender.rnkCommitment } } = base := by
  cases base
  rfl

theorem unregulated_sender_commitment_preserved (c : Crypto) (base : TransferSem.Witness)
    (i : RawInputs) (unregulated : base.regulated = false) :
    (construct c base i).sender.rnkCommitment = base.sender.rnkCommitment := by
  simp only [construct, provisional, senderCommitment, unregulated, Bool.false_eq_true, if_false]

theorem sender_commitment_canonical (c : Crypto) (base : TransferSem.Witness) (i : RawInputs)
    (cryptoCanonical : CanonicalCrypto c) (oldCanonical : base.sender.rnkCommitment < fieldModulus) :
    senderCommitment c base i < fieldModulus := by
  unfold senderCommitment
  split
  · exact cryptoCanonical.1 _ _
  · exact oldCanonical

theorem fieldsCanonical_append (a b : List Nat) :
    fieldsCanonical (a ++ b) ↔ fieldsCanonical a ∧ fieldsCanonical b := by
  simp only [fieldsCanonical, List.mem_append, or_imp, forall_and]

theorem canonical_witness_preserved (c : Crypto) (base : TransferSem.Witness)
    (i : RawInputs) (legal : LegalInputs c base i) (baseCanonical : CanonicalWitness base)
    (cryptoCanonical : CanonicalCrypto c) : CanonicalWitness (construct c base i) := by
  simp only [CanonicalWitness, fieldsCanonical_append] at baseCanonical ⊢
  rcases baseCanonical with
    ⟨⟨⟨⟨⟨⟨⟨⟨header, _⟩, _⟩, registry⟩, sender⟩, receiver⟩, notes⟩, volume⟩, encryption⟩
  have newHeader : fieldsCanonical
      [(construct c base i).anchor, (construct c base i).assetAnchor, (construct c base i).userAnchor,
       (construct c base i).asset, (construct c base i).timestamp, (construct c base i).nonce,
       (construct c base i).blinding, (construct c base i).paddingSeed, (construct c base i).auth.nk,
       (construct c base i).auth.ivk, (construct c base i).auth.quotient, (construct c base i).auth.randomizer,
       (construct c base i).routing.regulatedPrecision, (construct c base i).routing.unregulatedPrecision,
       (construct c base i).routing.height, (construct c base i).routing.parameterSet,
       (construct c base i).routing.tags 0, (construct c base i).routing.tags 1] := by
    simp only [construct, provisional, constructAuth, fieldsCanonical, List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp, false_implies, forall_const, and_true] at header ⊢
    rcases header with ⟨a, b, d, e, f, g, h, j, _, _, _, _, k, l, m, n, p, q⟩
    exact ⟨a, b, d, e, f, g, h, j, legal.nkCanonical,
      Nat.lt_trans (ivk_bounded c i) (by decide : scalarOrder < fieldModulus),
      Nat.lt_of_le_of_lt (quotient_bounded c i cryptoCanonical) (by decide : 8 < fieldModulus),
      Nat.lt_trans legal.randomizerBounded (by decide : scalarOrder < fieldModulus), k, l, m, n, p, q⟩
  have newSender : fieldsCanonical (userFields (construct c base i).sender) := by
    simp only [userFields, fieldsCanonical_append] at sender ⊢
    rcases sender with ⟨⟨⟨address, dh⟩, scalars⟩, path⟩
    simp only [fieldsCanonical, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
      false_implies, forall_const, and_true] at scalars
    exact ⟨⟨⟨address, dh⟩, by
      simpa only [construct, provisional, fieldsCanonical, List.mem_cons, List.not_mem_nil,
        forall_eq_or_imp, false_implies, forall_const, and_true] using
        And.intro (sender_commitment_canonical c base i cryptoCanonical scalars.1) scalars.2⟩, path⟩
  have ak : fieldsCanonical (pointFields i.ak) := by
    simpa only [pointFields, fieldsCanonical, List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp, false_implies, forall_const, and_true] using legal.akValid.1
  have rk : fieldsCanonical (pointFields (computedRK c i)) := by
    simpa only [computedRK, pointFields, fieldsCanonical, List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp, false_implies, forall_const, and_true] using cryptoCanonical.2.2.2.1 i.ak (c.mul i.randomizer c.generator)
  exact ⟨⟨⟨⟨⟨⟨⟨⟨newHeader, ak⟩, rk⟩, registry⟩, newSender⟩, receiver⟩, notes⟩, volume⟩, encryption⟩

set_option pp.all true in
#check @ivk_bounded
#print axioms ivk_bounded
set_option pp.all true in
#check @quotient_bounded
#print axioms quotient_bounded
set_option pp.all true in
#check @scalar_decomposition
#print axioms scalar_decomposition
set_option pp.all true in
#check @rk_valid
#print axioms rk_valid
set_option pp.all true in
#check @rnk_ignores_sender_commitment
#print axioms rnk_ignores_sender_commitment
set_option pp.all true in
#check @constructed_authorization_semantics
#print axioms constructed_authorization_semantics
set_option pp.all true in
#check @restore_full_record
#print axioms restore_full_record
set_option pp.all true in
#check @unregulated_sender_commitment_preserved
#print axioms unregulated_sender_commitment_preserved
set_option pp.all true in
#check @sender_commitment_canonical
#print axioms sender_commitment_canonical
set_option pp.all true in
#check @fieldsCanonical_append
#print axioms fieldsCanonical_append
set_option pp.all true in
#check @canonical_witness_preserved
#print axioms canonical_witness_preserved

end ShielddSecurity.TransferAuthorizationBranchCompletion
