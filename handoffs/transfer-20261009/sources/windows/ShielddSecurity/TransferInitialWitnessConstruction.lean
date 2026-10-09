import ShielddSecurity.TransferSem

set_option maxHeartbeats 200000

/-! Initial semantic storage from raw headers and address/key coordinates.
Every future computed component starts with explicit zero storage; canonicality
is derived from the raw bounds. This seed does not satisfy TransferSem and is
not a circuit assignment, authenticated membership proof or Rust constructor. -/
namespace ShielddSecurity.TransferInitialWitnessConstruction

open TransferCore TransferSem

structure Inputs where
  anchor : Nat
  assetAnchor : Nat
  userAnchor : Nat
  timestamp : Nat
  nonce : Nat
  blinding : Nat
  paddingSeed : Nat
  optionalDummy : Bool
  senderAddress : Address
  receiverAddress : Address
  senderRnkDH : Affine
  receiverRnkDH : Affine
  senderRnkCommitment : Nat
  receiverRnkCommitment : Nat

structure Legal (i : Inputs) : Prop where
  anchorCanonical : i.anchor < fieldModulus
  assetAnchorCanonical : i.assetAnchor < fieldModulus
  userAnchorCanonical : i.userAnchor < fieldModulus
  timestampBounded : i.timestamp < 2 ^ 64
  nonceCanonical : i.nonce < fieldModulus
  blindingBounded : i.blinding < scalarOrder
  paddingSeedCanonical : i.paddingSeed < fieldModulus
  senderDiversifiedCanonical : CanonicalAffine i.senderAddress.diversified
  senderTransmissionCanonical : CanonicalAffine i.senderAddress.transmission
  receiverDiversifiedCanonical : CanonicalAffine i.receiverAddress.diversified
  receiverTransmissionCanonical : CanonicalAffine i.receiverAddress.transmission
  senderRnkDHCanonical : CanonicalAffine i.senderRnkDH
  receiverRnkDHCanonical : CanonicalAffine i.receiverRnkDH
  senderRnkCommitmentCanonical : i.senderRnkCommitment < fieldModulus
  receiverRnkCommitmentCanonical : i.receiverRnkCommitment < fieldModulus

def zeroPoint : Affine := ⟨0, 0⟩
def zeroPath (depth : Nat) : Path depth := fun _ _ => 0

def initialUser (address : Address) (dh : Affine) (commitment : Nat) : User :=
  ⟨address, dh, commitment, 0, 0, zeroPath 16⟩

def zeroRegistry : AssetLeaf :=
  ⟨0, 0, 0, zeroPoint, 0, 0, zeroPoint, 0, 0, 0, 0,
    ⟨0, zeroPoint, zeroPoint⟩, 0, zeroPath 16⟩

def zeroAuthorization : Authorization := ⟨zeroPoint, 0, 0, 0, 0, zeroPoint⟩
def zeroSpend : Spend := ⟨0, 0, 0, 0, zeroPath 24, 0⟩
def zeroRecovery : Recovery := ⟨zeroPoint, 0, 0, 0, 0, 0, 0, 0, 0⟩
def zeroOutput : Output := ⟨0, 0, zeroRecovery, 0⟩
def zeroVolume : Volume :=
  ⟨0, 0, 0, 0, false, false, 0, 0, 0, 0, 0, 0, 0, zeroPath 24, 0, 0⟩
def zeroRouting : Routing := ⟨0, 0, 0, 0, fun _ => 0⟩
def zeroTier : Tier := ⟨0, zeroPoint, 0, fun _ => 0, 0⟩
def zeroOwnership : Ownership := ⟨0, zeroPoint, zeroPoint⟩
def zeroEncryption : Encryption :=
  ⟨fun _ => 0, fun _ => zeroTier, fun _ => 0, 0, fun _ => 0, 0, fun _ => zeroOwnership⟩

def construct (i : Inputs) : TransferSem.Witness :=
  { anchor := i.anchor, assetAnchor := i.assetAnchor, userAnchor := i.userAnchor,
    asset := 0, regulated := false, timestamp := i.timestamp, nonce := i.nonce,
    blinding := i.blinding, registry := zeroRegistry,
    sender := initialUser i.senderAddress i.senderRnkDH i.senderRnkCommitment,
    receiver := initialUser i.receiverAddress i.receiverRnkDH i.receiverRnkCommitment,
    auth := zeroAuthorization, spends := fun _ => zeroSpend, optionalDummy := i.optionalDummy,
    paddingSeed := i.paddingSeed, outputs := fun _ => zeroOutput,
    volume := zeroVolume, routing := zeroRouting, encryption := zeroEncryption }

private theorem zero_lt_field : 0 < fieldModulus := by decide

private theorem canonical_append (a b : List Nat) :
    fieldsCanonical (a ++ b) ↔ fieldsCanonical a ∧ fieldsCanonical b := by
  simp only [fieldsCanonical, List.mem_append, or_imp, forall_and]

private theorem canonical_point (p : Affine) (canonical : CanonicalAffine p) :
    fieldsCanonical (pointFields p) := by
  simpa [pointFields, fieldsCanonical, CanonicalAffine] using canonical

private theorem canonical_zero_path (depth : Nat) :
    fieldsCanonical (pathFields (zeroPath depth)) := by
  intro value member
  rcases List.mem_flatMap.mp member with ⟨level, _, member⟩
  rcases List.mem_map.mp member with ⟨slot, _, equal⟩
  have : value = 0 := equal.symm
  simpa [this] using zero_lt_field

private theorem canonical_initial_user (address : Address) (dh : Affine) (commitment : Nat)
    (diversified : CanonicalAffine address.diversified)
    (transmission : CanonicalAffine address.transmission) (dhCanonical : CanonicalAffine dh)
    (commitmentCanonical : commitment < fieldModulus) :
    fieldsCanonical (userFields (initialUser address dh commitment)) := by
  have path := canonical_zero_path 16
  have d := canonical_point address.diversified diversified
  have t := canonical_point address.transmission transmission
  have k := canonical_point dh dhCanonical
  have scalars : fieldsCanonical [commitment, 0, 0] := by
    simpa [fieldsCanonical, zero_lt_field] using commitmentCanonical
  simp only [userFields, initialUser, addressFields, canonical_append]
  exact ⟨⟨⟨⟨d, t⟩, k⟩, scalars⟩, path⟩

private theorem canonical_zero_registry : fieldsCanonical (registryFields zeroRegistry) := by
  simp only [registryFields, zeroRegistry, pointFields, zeroPoint, canonical_append,
    canonical_zero_path]
  simp [fieldsCanonical, zero_lt_field]

private theorem canonical_zero_notes : fieldsCanonical ((List.finRange 2).flatMap
    (fun _ => spendFields zeroSpend ++ outputFields zeroOutput)) := by
  intro value member
  rcases List.mem_flatMap.mp member with ⟨_, _, member⟩
  have canonical : fieldsCanonical (spendFields zeroSpend ++ outputFields zeroOutput) := by
    simp only [spendFields, outputFields, recoveryFields, zeroSpend, zeroOutput, zeroRecovery,
      pointFields, zeroPoint, canonical_append, canonical_zero_path]
    simp [fieldsCanonical, zero_lt_field]
  exact canonical value member

private theorem canonical_zero_volume : fieldsCanonical (volumeFields zeroVolume) := by
  simp only [volumeFields, zeroVolume, canonical_append, canonical_zero_path]
  simp [fieldsCanonical, zero_lt_field]

private theorem canonical_zero_encryption : fieldsCanonical (encryptionFields zeroEncryption) := by
  intro value member
  simp only [encryptionFields, zeroEncryption, List.mem_append] at member
  rcases member with (member | member) | member
  · rcases List.mem_flatMap.mp member with ⟨_, _, member⟩
    simp only [zeroTier, pointFields, zeroPoint, List.mem_append] at member
    rcases member with (member | member) | member
    · exact (by simp [fieldsCanonical, zero_lt_field] :
        fieldsCanonical [0, 0, 0, 0, 0, 0]) value member
    · exact (by simp [fieldsCanonical, zero_lt_field] : fieldsCanonical [0, 0]) value member
    · rcases List.mem_map.mp member with ⟨_, _, equal⟩
      simpa [← equal] using zero_lt_field
  · exact (by simp [fieldsCanonical, zero_lt_field] : fieldsCanonical [0, 0]) value member
  · rcases List.mem_flatMap.mp member with ⟨_, _, member⟩
    exact (by simp [zeroOwnership, pointFields, zeroPoint, fieldsCanonical, zero_lt_field] :
      fieldsCanonical ([zeroOwnership.randomness] ++ pointFields zeroOwnership.r ++
        pointFields zeroOwnership.c)) value member

theorem constructed_canonical (i : Inputs) (legal : Legal i) :
    CanonicalWitness (construct i) := by
  have timeField : i.timestamp < fieldModulus :=
    Nat.lt_trans legal.timestampBounded (by decide : 2 ^ 64 < fieldModulus)
  have blindingField : i.blinding < fieldModulus :=
    Nat.lt_trans legal.blindingBounded (by decide : scalarOrder < fieldModulus)
  have header : fieldsCanonical
      [i.anchor, i.assetAnchor, i.userAnchor, 0, i.timestamp, i.nonce, i.blinding,
        i.paddingSeed, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    simp only [fieldsCanonical, List.mem_cons, List.not_mem_nil, forall_eq_or_imp,
      false_implies, forall_const, and_true]
    exact ⟨legal.anchorCanonical, legal.assetAnchorCanonical, legal.userAnchorCanonical,
      zero_lt_field, timeField, legal.nonceCanonical, blindingField, legal.paddingSeedCanonical,
      zero_lt_field, zero_lt_field, zero_lt_field, zero_lt_field, zero_lt_field,
      zero_lt_field, zero_lt_field, zero_lt_field, zero_lt_field, zero_lt_field⟩
  have point : fieldsCanonical (pointFields zeroPoint) := by
    simp [pointFields, zeroPoint, fieldsCanonical, zero_lt_field]
  have sender := canonical_initial_user i.senderAddress i.senderRnkDH i.senderRnkCommitment
    legal.senderDiversifiedCanonical legal.senderTransmissionCanonical legal.senderRnkDHCanonical
    legal.senderRnkCommitmentCanonical
  have receiver := canonical_initial_user i.receiverAddress i.receiverRnkDH i.receiverRnkCommitment
    legal.receiverDiversifiedCanonical legal.receiverTransmissionCanonical legal.receiverRnkDHCanonical
    legal.receiverRnkCommitmentCanonical
  simp only [CanonicalWitness, construct, zeroAuthorization, zeroRouting, canonical_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨header, point⟩, point⟩, canonical_zero_registry⟩, sender⟩,
    receiver⟩, canonical_zero_notes⟩, canonical_zero_volume⟩, canonical_zero_encryption⟩

theorem raw_header_and_keys_preserved (i : Inputs) :
    (construct i).anchor = i.anchor ∧ (construct i).assetAnchor = i.assetAnchor ∧
    (construct i).userAnchor = i.userAnchor ∧ (construct i).timestamp = i.timestamp ∧
    (construct i).nonce = i.nonce ∧ (construct i).blinding = i.blinding ∧
    (construct i).paddingSeed = i.paddingSeed ∧
    (construct i).sender.address = i.senderAddress ∧
    (construct i).receiver.address = i.receiverAddress ∧
    (construct i).sender.rnkDH = i.senderRnkDH ∧
    (construct i).receiver.rnkDH = i.receiverRnkDH ∧
    (construct i).sender.rnkCommitment = i.senderRnkCommitment ∧
    (construct i).receiver.rnkCommitment = i.receiverRnkCommitment ∧
    (construct i).optionalDummy = i.optionalDummy :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem seed_is_not_transfer_sem (c : Crypto) (i : Inputs) :
    ¬ TransferSem.TransferSem c (construct i) := by
  intro accepted
  have assetNonzero := accepted.2.1.2.2.2.1.2.2.1
  exact assetNonzero rfl

set_option pp.all true in
#check @constructed_canonical
#print axioms constructed_canonical
set_option pp.all true in
#check @raw_header_and_keys_preserved
#print axioms raw_header_and_keys_preserved
set_option pp.all true in
#check @seed_is_not_transfer_sem
#print axioms seed_is_not_transfer_sem

end ShielddSecurity.TransferInitialWitnessConstruction
