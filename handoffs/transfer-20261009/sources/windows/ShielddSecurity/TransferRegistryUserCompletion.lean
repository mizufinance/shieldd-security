import ShielddSecurity.TransferSem

set_option maxHeartbeats 200000

/-! Raw authenticated registry lookup and compliance path construction. These
stages do not assume RegistrySem/UserSem, desired hash outputs, or TransferSem.
External membership paths remain legal-input assumptions. Their interpretation
as the pinned hash/tree, arbitrary-row extraction and Rust refinement are open.
Registry construction precedes authorization; compliance construction follows
authorization so the sender path binds its final computed RNK commitment. -/
namespace ShielddSecurity.TransferRegistryUserCompletion

open TransferCore TransferSem

theorem fieldsCanonical_append (a b : List Nat) :
    fieldsCanonical (a ++ b) ↔ fieldsCanonical a ∧ fieldsCanonical b := by
  simp only [fieldsCanonical, List.mem_append, or_imp, forall_and]

structure RegistryInputs (c : Crypto) (base : TransferSem.Witness) where
  leaf : AssetLeaf
  regulated : Bool
  gapAsset : Nat
  detectionValid : ValidPoint c leaf.detection
  ringValid : ValidPoint c leaf.ring
  payloadValid : ValidPoint c leaf.audit.payload
  checkingValid : ValidPoint c leaf.audit.checking
  epochBounded : leaf.audit.epoch < 2 ^ 64
  positionBounded : leaf.position < 2 ^ 32
  valueCanonical : leaf.value < fieldModulus
  nextValueCanonical : leaf.nextValue < fieldModulus
  gapAssetCanonical : gapAsset < fieldModulus
  leafCanonical : fieldsCanonical (registryFields leaf)
  authenticated : root c .asset leaf.position (assetLeaf c leaf) leaf.siblings = base.assetAnchor
  activeAudit : regulated = true →
    leaf.audit.epoch ≠ 0 ∧ nonidentity leaf.audit.payload ∧ nonidentity leaf.audit.checking ∧
    leaf.audit.payload ≠ c.unregulatedRing ∧ leaf.audit.checking ≠ c.unregulatedRing ∧
    leaf.audit.payload ≠ leaf.audit.checking
  strictGap : regulated = false → leaf.value < gapAsset ∧ gapAsset < leaf.nextValue

def selectedAsset (c : Crypto) (base : TransferSem.Witness) (i : RegistryInputs c base) : Nat :=
  if i.regulated then i.leaf.value else i.gapAsset

def constructRegistry (c : Crypto) (base : TransferSem.Witness) (i : RegistryInputs c base) :
    TransferSem.Witness :=
  { base with registry := i.leaf, regulated := i.regulated, asset := selectedAsset c base i }

theorem selected_asset_canonical (c : Crypto) (base : TransferSem.Witness)
    (i : RegistryInputs c base) : selectedAsset c base i < fieldModulus := by
  cases h : i.regulated with
  | false => simpa [selectedAsset, h] using i.gapAssetCanonical
  | true => simpa [selectedAsset, h] using i.valueCanonical

theorem constructed_registry_semantics (c : Crypto) (base : TransferSem.Witness)
    (i : RegistryInputs c base) : RegistrySem c (constructRegistry c base i) := by
  refine ⟨i.detectionValid, i.ringValid, i.payloadValid, i.checkingValid,
    i.epochBounded, i.positionBounded, i.valueCanonical, selected_asset_canonical c base i,
    i.nextValueCanonical, i.authenticated, ?_⟩
  cases h : i.regulated with
  | false => simpa [constructRegistry, selectedAsset, h] using i.strictGap h
  | true => simpa [constructRegistry, selectedAsset, h] using
      And.intro (rfl : i.leaf.value = i.leaf.value) (i.activeAudit h)

theorem registry_full_frame (c : Crypto) (base : TransferSem.Witness)
    (i : RegistryInputs c base) :
    { constructRegistry c base i with
      registry := base.registry
      regulated := base.regulated
      asset := base.asset } = base := by
  cases base
  rfl

theorem registry_canonical_preserved (c : Crypto) (base : TransferSem.Witness)
    (i : RegistryInputs c base) (baseCanonical : CanonicalWitness base) :
    CanonicalWitness (constructRegistry c base i) := by
  simp only [CanonicalWitness, fieldsCanonical_append] at baseCanonical ⊢
  rcases baseCanonical with
    ⟨⟨⟨⟨⟨⟨⟨⟨header, ak⟩, rk⟩, _⟩, sender⟩, receiver⟩, notes⟩, volume⟩, encryption⟩
  have newHeader : fieldsCanonical
      [(constructRegistry c base i).anchor, (constructRegistry c base i).assetAnchor,
      (constructRegistry c base i).userAnchor, (constructRegistry c base i).asset,
      (constructRegistry c base i).timestamp, (constructRegistry c base i).nonce,
      (constructRegistry c base i).blinding, (constructRegistry c base i).paddingSeed,
      (constructRegistry c base i).auth.nk, (constructRegistry c base i).auth.ivk,
      (constructRegistry c base i).auth.quotient, (constructRegistry c base i).auth.randomizer,
      (constructRegistry c base i).routing.regulatedPrecision,
      (constructRegistry c base i).routing.unregulatedPrecision,
      (constructRegistry c base i).routing.height, (constructRegistry c base i).routing.parameterSet,
      (constructRegistry c base i).routing.tags 0, (constructRegistry c base i).routing.tags 1] := by
    simp only [constructRegistry, fieldsCanonical, List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp, false_implies, forall_const, and_true] at header ⊢
    rcases header with ⟨a, b, d, _, e, f, g, h, j, k, l, m, n, o, p, q, r, s⟩
    exact ⟨a, b, d, selected_asset_canonical c base i, e, f, g, h, j, k, l, m, n, o, p, q, r, s⟩
  exact ⟨⟨⟨⟨⟨⟨⟨⟨newHeader, ak⟩, rk⟩, i.leafCanonical⟩, sender⟩, receiver⟩, notes⟩, volume⟩, encryption⟩

structure UserPathInputs where
  freezeGeneration : Nat
  inactiveLifecycle : Nat
  position : Nat
  siblings : Path 16

def constructUser (regulated : Bool) (old : User) (i : UserPathInputs) : User :=
  { old with
    lifecycle := if regulated then 1 + 8 * i.freezeGeneration else i.inactiveLifecycle
    position := i.position
    siblings := i.siblings }

structure LegalUserPath (c : Crypto) (base : TransferSem.Witness) (old : User)
    (i : UserPathInputs) : Prop where
  diversifiedValid : ValidPoint c old.address.diversified
  diversifiedNonidentity : nonidentity old.address.diversified
  transmissionValid : ValidPoint c old.address.transmission
  transmissionNonidentity : nonidentity old.address.transmission
  rnkDHValid : ValidPoint c old.rnkDH
  rnkDHNonidentity : nonidentity old.rnkDH
  generationBounded : i.freezeGeneration < 2 ^ 64
  inactiveLifecycleBounded : i.inactiveLifecycle < 2 ^ 131
  positionBounded : i.position < 2 ^ 32
  siblingsCanonical : fieldsCanonical (pathFields i.siblings)
  authenticated : base.regulated = true →
    root c .compliance i.position (userLeaf c base.asset (constructUser base.regulated old i))
      i.siblings = base.userAnchor

theorem constructed_active_lifecycle (generation : Nat) (bounded : generation < 2 ^ 64) :
    (1 + 8 * generation) % 8 = 1 ∧ (1 + 8 * generation) / 2 ^ 67 = 0 ∧
    1 + 8 * generation < 2 ^ 131 := by
  change generation < 18446744073709551616 at bounded
  have low : 1 + 8 * generation < 2 ^ 67 := by
    change 1 + 8 * generation < 147573952589676412928
    omega
  refine ⟨?_, Nat.div_eq_of_lt low, Nat.lt_trans low (by decide : 2 ^ 67 < 2 ^ 131)⟩
  simp [Nat.add_mod, Nat.mul_mod]

theorem constructed_user_semantics (c : Crypto) (base : TransferSem.Witness) (old : User)
    (i : UserPathInputs) (legal : LegalUserPath c base old i) :
    UserSem c base (constructUser base.regulated old i) := by
  have active := constructed_active_lifecycle i.freezeGeneration legal.generationBounded
  refine ⟨legal.diversifiedValid, legal.diversifiedNonidentity, legal.transmissionValid,
    legal.transmissionNonidentity, legal.rnkDHValid, legal.rnkDHNonidentity, ?_,
    legal.positionBounded, ?_⟩
  · cases h : base.regulated with
    | false => simpa [constructUser, h] using legal.inactiveLifecycleBounded
    | true => simpa [constructUser, h] using active.2.2
  · intro enabled
    simpa [constructUser, enabled] using
      And.intro active.1 (And.intro active.2.1 (legal.authenticated enabled))

theorem user_key_frame (regulated : Bool) (old : User) (i : UserPathInputs) :
    (constructUser regulated old i).address = old.address ∧
    (constructUser regulated old i).rnkDH = old.rnkDH ∧
    (constructUser regulated old i).rnkCommitment = old.rnkCommitment := ⟨rfl, rfl, rfl⟩

theorem constructed_user_canonical (c : Crypto) (base : TransferSem.Witness) (old : User)
    (i : UserPathInputs) (legal : LegalUserPath c base old i)
    (oldCanonical : fieldsCanonical (userFields old)) :
    fieldsCanonical (userFields (constructUser base.regulated old i)) := by
  have lifecycleBound := (constructed_user_semantics c base old i legal).2.2.2.2.2.2.1
  have lifecycleField : 2 ^ 131 < fieldModulus := by decide
  have positionField : 2 ^ 32 < fieldModulus := by decide
  simp only [userFields, fieldsCanonical_append] at oldCanonical ⊢
  rcases oldCanonical with ⟨⟨⟨address, dh⟩, scalars⟩, _⟩
  have commitmentBound : old.rnkCommitment < fieldModulus :=
    scalars old.rnkCommitment (by simp)
  refine ⟨⟨⟨address, dh⟩, ?_⟩, legal.siblingsCanonical⟩
  simp only [constructUser, fieldsCanonical, List.mem_cons, List.not_mem_nil,
    forall_eq_or_imp, false_implies, forall_const, and_true]
  exact ⟨commitmentBound, Nat.lt_trans lifecycleBound lifecycleField,
    Nat.lt_trans legal.positionBounded positionField⟩

def constructUsers (base : TransferSem.Witness) (sender receiver : UserPathInputs) :
    TransferSem.Witness :=
  { base with
    sender := constructUser base.regulated base.sender sender
    receiver := constructUser base.regulated base.receiver receiver }

theorem constructed_both_users (c : Crypto) (base : TransferSem.Witness)
    (sender receiver : UserPathInputs)
    (senderLegal : LegalUserPath c base base.sender sender)
    (receiverLegal : LegalUserPath c base base.receiver receiver) :
    UserSem c (constructUsers base sender receiver) (constructUsers base sender receiver).sender ∧
    UserSem c (constructUsers base sender receiver) (constructUsers base sender receiver).receiver :=
  ⟨constructed_user_semantics c base base.sender sender senderLegal,
    constructed_user_semantics c base base.receiver receiver receiverLegal⟩

theorem users_preserve_registry_auth_spends (c : Crypto) (base : TransferSem.Witness)
    (sender receiver : UserPathInputs) :
    (RegistrySem c (constructUsers base sender receiver) = RegistrySem c base) ∧
    (AuthorizationSem c (constructUsers base sender receiver) = AuthorizationSem c base) ∧
    ((∀ slot, SpendSem c (constructUsers base sender receiver) slot) =
      (∀ slot, SpendSem c base slot)) := ⟨rfl, rfl, rfl⟩

theorem users_full_frame (base : TransferSem.Witness) (sender receiver : UserPathInputs) :
    { constructUsers base sender receiver with sender := base.sender, receiver := base.receiver } =
      base := by
  cases base
  rfl

theorem users_canonical_preserved (c : Crypto) (base : TransferSem.Witness)
    (sender receiver : UserPathInputs)
    (senderLegal : LegalUserPath c base base.sender sender)
    (receiverLegal : LegalUserPath c base base.receiver receiver)
    (baseCanonical : CanonicalWitness base) :
    CanonicalWitness (constructUsers base sender receiver) := by
  simp only [CanonicalWitness, fieldsCanonical_append] at baseCanonical ⊢
  rcases baseCanonical with
    ⟨⟨⟨⟨⟨⟨⟨⟨header, ak⟩, rk⟩, registry⟩, oldSender⟩, oldReceiver⟩, notes⟩, volume⟩, encryption⟩
  exact ⟨⟨⟨⟨⟨⟨⟨⟨header, ak⟩, rk⟩, registry⟩,
    constructed_user_canonical c base base.sender sender senderLegal oldSender⟩,
    constructed_user_canonical c base base.receiver receiver receiverLegal oldReceiver⟩,
    notes⟩, volume⟩, encryption⟩

theorem refuse_equal_gap_endpoint (c : Crypto) (w : TransferSem.Witness)
    (unregulated : w.regulated = false) (endpoint : w.asset = w.registry.value) :
    ¬ RegistrySem c w := by
  intro accepted
  have branch := accepted.2.2.2.2.2.2.2.2.2.2
  simp only [unregulated, Bool.false_eq_true, ↓reduceIte] at branch
  have low := branch.1
  rw [endpoint] at low
  exact Nat.lt_irrefl _ low

theorem refuse_regulated_inactive_lifecycle (c : Crypto) (w : TransferSem.Witness) (u : User)
    (regulated : w.regulated = true) (inactive : u.lifecycle % 8 ≠ 1) :
    ¬ UserSem c w u := by
  intro accepted
  exact inactive ((accepted.2.2.2.2.2.2.2.2 regulated).1)

set_option pp.all true in
#check @fieldsCanonical_append
#print axioms fieldsCanonical_append
set_option pp.all true in
#check @selected_asset_canonical
#print axioms selected_asset_canonical
set_option pp.all true in
#check @constructed_registry_semantics
#print axioms constructed_registry_semantics
set_option pp.all true in
#check @registry_full_frame
#print axioms registry_full_frame
set_option pp.all true in
#check @registry_canonical_preserved
#print axioms registry_canonical_preserved
set_option pp.all true in
#check @constructed_active_lifecycle
#print axioms constructed_active_lifecycle
set_option pp.all true in
#check @constructed_user_semantics
#print axioms constructed_user_semantics
set_option pp.all true in
#check @user_key_frame
#print axioms user_key_frame
set_option pp.all true in
#check @constructed_user_canonical
#print axioms constructed_user_canonical
set_option pp.all true in
#check @constructed_both_users
#print axioms constructed_both_users
set_option pp.all true in
#check @users_preserve_registry_auth_spends
#print axioms users_preserve_registry_auth_spends
set_option pp.all true in
#check @users_full_frame
#print axioms users_full_frame
set_option pp.all true in
#check @users_canonical_preserved
#print axioms users_canonical_preserved
set_option pp.all true in
#check @refuse_equal_gap_endpoint
#print axioms refuse_equal_gap_endpoint
set_option pp.all true in
#check @refuse_regulated_inactive_lifecycle
#print axioms refuse_regulated_inactive_lifecycle

end ShielddSecurity.TransferRegistryUserCompletion
