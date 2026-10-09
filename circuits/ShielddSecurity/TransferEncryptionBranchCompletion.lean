import ShielddSecurity.TransferSem

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferEncryptionBranchCompletion
open TransferSem TransferCore

structure LegalEncryptionInputs (c : Crypto) (base : TransferSem.Witness) where
  seeds : Fin 4 → Nat
  ephemeral : Fin 4 → Nat
  ownershipRandomness : Fin 2 → Nat
  seedCanonical : ∀ i, seeds i < fieldModulus
  ephemeralBounded : ∀ i, ephemeral i < scalarOrder
  ephemeralNonzero : ∀ i, ephemeral i ≠ 0
  ownershipBounded : ∀ i, ownershipRandomness i < scalarOrder
  ownershipNonzero : ∀ i, ownershipRandomness i ≠ 0
  epkNonidentity : ∀ i, nonidentity (c.mul (ephemeral i) c.generator)
  ownershipNonidentity : ∀ i, nonidentity (c.mul (ownershipRandomness i) c.generator)
  detectionNonidentity : nonidentity (detectionKey c base)
  checkingNonidentity : nonidentity (checkingKey c base)

def selectedKey (c : Crypto) (base : TransferSem.Witness) : Affine :=
  if flagged base then detectionKey c base else payloadKey c base

def constructTier (c : Crypto) (base : TransferSem.Witness)
    (i : LegalEncryptionInputs c base) (slot : Fin 4) : Tier :=
  let epk := c.mul (i.ephemeral slot) c.generator
  { ephemeral := i.ephemeral slot, epk := epk,
    c2 := fadd (i.seeds slot) (secret c (c.mul (i.ephemeral slot) (selectedKey c base))),
    confirmation := if slot.val = 0 ∨ slot.val = 2 then
      c.hash .keyConfirmation ([i.seeds slot] ++ pointFields epk ++ [salt c base (slot.val+1)]) else 0,
    ciphertext := fun j => if slot.val = 0 ∨ slot.val = 2 then
      if j.val = 0 then fadd (base.outputs 0).amount (stream c (i.seeds slot) 0) else 0
      else fadd (c.addressWords (if slot.val = 1 then base.receiver.address else base.sender.address) j)
        (stream c (i.seeds slot) j.val) }

def constructOwnership (c : Crypto) (base : TransferSem.Witness)
    (i : LegalEncryptionInputs c base) (slot : Fin 2) : Ownership :=
  { randomness := i.ownershipRandomness slot,
    r := c.mul (i.ownershipRandomness slot) c.generator,
    c := c.add (c.fingerprint (if slot.val = 0 then base.sender.address else base.receiver.address))
      (c.mul (i.ownershipRandomness slot) (checkingKey c base)) }

def detectionSeed (c : Crypto) (base : TransferSem.Witness)
    (i : LegalEncryptionInputs c base) : Nat :=
  c.hash .detection (pointFields (c.mul (i.ephemeral 0) (detectionKey c base)) ++
    pointFields (c.mul (i.ephemeral 0) c.generator))

def construct (c : Crypto) (base : TransferSem.Witness)
    (i : LegalEncryptionInputs c base) : Encryption :=
  { timestamp := base.timestamp,
    auditEpoch := if base.regulated then base.registry.audit.epoch else 0,
    policy := fun slot => if base.regulated then
      [base.registry.ringID,base.registry.policyID,base.registry.resource,base.registry.permission][slot.val]!
      else c.emptyPolicy,
    salts := fun slot => salt c base (slot.val+1),
    detection := fun slot => fadd
      ([base.asset,salt c base 0,if flagged base then 1 else 0,0][slot.val]!)
      (stream c (detectionSeed c base i) slot.val),
    tiers := constructTier c base i, ownership := constructOwnership c base i }

theorem fadd_canonical (a b : Nat) : fadd a b < fieldModulus :=
  Nat.mod_lt _ (by decide)

theorem fsub_canonical (a b : Nat) : fsub a b < fieldModulus :=
  Nat.mod_lt _ (by decide)

theorem fsub_fadd_cancel (seed shared : Nat) (canonical : seed < fieldModulus) :
    fsub (fadd seed shared) shared = seed := by
  have modulusPositive : 0 < fieldModulus := by decide
  have remainderBound : shared % fieldModulus < fieldModulus := Nat.mod_lt _ modulusPositive
  unfold fsub fadd
  rw [Nat.add_mod, Nat.mod_eq_of_lt canonical]
  simp only [Nat.mod_mod]
  by_cases small : seed + shared % fieldModulus < fieldModulus
  · rw [Nat.mod_eq_of_lt small]
    have cancel : seed + shared % fieldModulus + fieldModulus - shared % fieldModulus =
        seed + fieldModulus := by omega
    rw [cancel,Nat.add_mod_right,Nat.mod_eq_of_lt canonical]
  · have large : fieldModulus ≤ seed + shared % fieldModulus := by omega
    have reduced : seed + shared % fieldModulus - fieldModulus < fieldModulus := by omega
    rw [Nat.mod_eq_sub_mod large,Nat.mod_eq_of_lt reduced]
    have cancel : seed + shared % fieldModulus - fieldModulus + fieldModulus -
        shared % fieldModulus = seed := by omega
    rw [cancel,Nat.mod_eq_of_lt canonical]

theorem constructed_tier_seed (c : Crypto) (base : TransferSem.Witness)
    (i : LegalEncryptionInputs c base) (slot : Fin 4) :
    fsub (constructTier c base i slot).c2
      (secret c (c.mul (constructTier c base i slot).ephemeral (selectedKey c base))) = i.seeds slot :=
  fsub_fadd_cancel _ _ (i.seedCanonical slot)

theorem constructed_tier_semantics (c : Crypto) (base : TransferSem.Witness)
    (i : LegalEncryptionInputs c base) (slot : Fin 4) :
    let tier := constructTier c base i slot
    let seed := fsub tier.c2 (secret c (c.mul tier.ephemeral (selectedKey c base)))
    tier.ephemeral < scalarOrder ∧ tier.epk = c.mul tier.ephemeral c.generator ∧ nonidentity tier.epk ∧
    (if slot.val = 0 ∨ slot.val = 2 then
      tier.confirmation = c.hash .keyConfirmation ([seed] ++ pointFields tier.epk ++ [salt c base (slot.val+1)]) ∧
      tier.ciphertext 0 = fadd (base.outputs 0).amount (stream c seed 0)
     else ∀ j : Fin 3, tier.ciphertext j =
       fadd (c.addressWords (if slot.val = 1 then base.receiver.address else base.sender.address) j)
         (stream c seed j.val)) := by
  dsimp only
  rw [constructed_tier_seed]
  refine ⟨i.ephemeralBounded slot,rfl,i.epkNonidentity slot,?_⟩
  by_cases core : slot.val = 0 ∨ slot.val = 2
  · simp only [constructTier,if_pos core]
    exact ⟨True.intro,rfl⟩
  · simp only [constructTier,if_neg core]
    intro j
    exact True.intro

theorem constructed_encryption_semantics (c : Crypto) (base : TransferSem.Witness)
    (i : LegalEncryptionInputs c base) :
    EncryptionSem c {base with encryption := construct c base i} := by
  refine ⟨i.detectionNonidentity,rfl,rfl,(fun _ => rfl),(fun _ => rfl),(fun _ => rfl),?_,?_⟩
  · intro slot
    exact constructed_tier_semantics c base i slot
  · intro slot
    exact ⟨i.ownershipBounded slot,rfl,i.ownershipNonidentity slot,i.checkingNonidentity,rfl⟩

theorem restore_full_record (c : Crypto) (base : TransferSem.Witness)
    (i : LegalEncryptionInputs c base) :
    {{base with encryption := construct c base i} with encryption := base.encryption} = base := by
  cases base
  rfl

theorem fieldsCanonical_append (a b : List Nat) :
    fieldsCanonical (a ++ b) ↔ fieldsCanonical a ∧ fieldsCanonical b := by
  simp only [fieldsCanonical,List.mem_append,or_imp,forall_and]

theorem canonical_list_lookup (fields : List Nat) (canonical : fieldsCanonical fields)
    (index : Nat) (bounded : index < fields.length) : fields[index]! < fieldModulus := by
  rw [getElem!_pos fields index bounded]
  exact canonical _ (List.getElem_mem bounded)

theorem canonical_constructed_ciphertext (c : Crypto) (base : TransferSem.Witness)
    (i : LegalEncryptionInputs c base) (slot : Fin 4) (j : Fin 3) :
    (constructTier c base i slot).ciphertext j < fieldModulus := by
  dsimp only [constructTier]
  split
  · split
    · exact fadd_canonical _ _
    · decide
  · exact fadd_canonical _ _

theorem canonical_constructed_confirmation (c : Crypto) (base : TransferSem.Witness)
    (i : LegalEncryptionInputs c base) (slot : Fin 4) (cryptoCanonical : CanonicalCrypto c) :
    (constructTier c base i slot).confirmation < fieldModulus := by
  dsimp only [constructTier]
  split
  · exact cryptoCanonical.1 _ _
  · decide

theorem canonical_constructed_encryption_fields (c : Crypto) (base : TransferSem.Witness)
    (i : LegalEncryptionInputs c base) (baseCanonical : CanonicalWitness base)
    (cryptoCanonical : CanonicalCrypto c) :
    fieldsCanonical (encryptionFields (construct c base i)) := by
  have baseBlocks := baseCanonical
  simp only [CanonicalWitness,fieldsCanonical_append] at baseBlocks
  rcases baseBlocks with
    ⟨⟨⟨⟨⟨⟨⟨⟨header,_ak⟩,_rk⟩,registry⟩,_sender⟩,_receiver⟩,_notes⟩,_volume⟩,_encryption⟩
  have zeroField : 0 < fieldModulus := by decide
  have scalarField : scalarOrder < fieldModulus := by decide
  have policyWords : fieldsCanonical
      [base.registry.ringID,base.registry.policyID,base.registry.resource,base.registry.permission] := by
    intro value member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;>
      apply registry <;> simp [registryFields]
  have policyCanonical : ∀ slot : Fin 4, (construct c base i).policy slot < fieldModulus := by
    intro slot
    dsimp only [construct]
    split
    · exact canonical_list_lookup _ policyWords slot.val (by exact slot.isLt)
    · exact cryptoCanonical.2.2.2.2.2.2.2.2.2.2
  have timestampCanonical : (construct c base i).timestamp < fieldModulus :=
    header _ (by simp [construct])
  have epochCanonical : (construct c base i).auditEpoch < fieldModulus := by
    dsimp only [construct]
    split
    · exact registry _ (by simp [registryFields])
    · exact zeroField
  have tierBlocks : ∀ slot : Fin 4, fieldsCanonical
      ([(construct c base i).detection slot,(construct c base i).policy slot,
        (construct c base i).salts slot,(constructTier c base i slot).ephemeral,
        (constructTier c base i slot).c2,(constructTier c base i slot).confirmation] ++
        pointFields (constructTier c base i slot).epk ++
        (List.finRange 3).map (constructTier c base i slot).ciphertext) := by
    intro slot
    rw [fieldsCanonical_append,fieldsCanonical_append]
    refine ⟨⟨?_,?_⟩,?_⟩
    · simp only [fieldsCanonical,List.mem_cons,List.not_mem_nil,
        forall_eq_or_imp,false_implies,forall_const,and_true]
      exact ⟨fadd_canonical _ _,policyCanonical slot,cryptoCanonical.1 _ _,
        Nat.lt_trans (i.ephemeralBounded slot) scalarField,fadd_canonical _ _,
        canonical_constructed_confirmation c base i slot cryptoCanonical⟩
    · have epk := cryptoCanonical.2.2.1 (i.ephemeral slot) c.generator
      simp only [constructTier,pointFields,fieldsCanonical,List.mem_cons,List.not_mem_nil,
        forall_eq_or_imp,false_implies,forall_const,and_true]
      exact epk
    · intro value member
      rcases List.mem_map.mp member with ⟨j,_jMember,rfl⟩
      exact canonical_constructed_ciphertext c base i slot j
  have ownershipBlocks : ∀ slot : Fin 2, fieldsCanonical
      ([(constructOwnership c base i slot).randomness] ++ pointFields (constructOwnership c base i slot).r ++
        pointFields (constructOwnership c base i slot).c) := by
    intro slot
    rw [fieldsCanonical_append,fieldsCanonical_append]
    refine ⟨⟨?_,?_⟩,?_⟩
    · simp only [fieldsCanonical,List.mem_cons,List.not_mem_nil,
        forall_eq_or_imp,false_implies,forall_const,and_true]
      exact Nat.lt_trans (i.ownershipBounded slot) scalarField
    · have rCanonical := cryptoCanonical.2.2.1 (i.ownershipRandomness slot) c.generator
      simp only [constructOwnership,pointFields,fieldsCanonical,List.mem_cons,List.not_mem_nil,
        forall_eq_or_imp,false_implies,forall_const,and_true]
      exact rCanonical
    · have cCanonical := cryptoCanonical.2.2.2.1
        (c.fingerprint (if slot.val = 0 then base.sender.address else base.receiver.address))
        (c.mul (i.ownershipRandomness slot) (checkingKey c base))
      simp only [constructOwnership,pointFields,fieldsCanonical,List.mem_cons,List.not_mem_nil,
        forall_eq_or_imp,false_implies,forall_const,and_true]
      exact cCanonical
  simp only [encryptionFields,fieldsCanonical_append]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro value member
    rcases List.mem_flatMap.mp member with ⟨slot,_slotMem,valueMem⟩
    exact tierBlocks slot value valueMem
  · simp only [fieldsCanonical,List.mem_cons,List.not_mem_nil,
      forall_eq_or_imp,false_implies,forall_const,and_true]
    exact ⟨timestampCanonical,epochCanonical⟩
  · intro value member
    rcases List.mem_flatMap.mp member with ⟨slot,_slotMem,valueMem⟩
    exact ownershipBlocks slot value valueMem

theorem canonical_witness_preserved (c : Crypto) (base : TransferSem.Witness)
    (i : LegalEncryptionInputs c base) (baseCanonical : CanonicalWitness base)
    (cryptoCanonical : CanonicalCrypto c) :
    CanonicalWitness {base with encryption := construct c base i} := by
  have encryptionCanonical := canonical_constructed_encryption_fields c base i baseCanonical cryptoCanonical
  simp only [CanonicalWitness,fieldsCanonical_append] at baseCanonical ⊢
  exact ⟨baseCanonical.1,encryptionCanonical⟩

theorem constructed_canonical_encryption_semantics (c : Crypto) (base : TransferSem.Witness)
    (i : LegalEncryptionInputs c base) (baseCanonical : CanonicalWitness base)
    (cryptoCanonical : CanonicalCrypto c) :
    CanonicalWitness {base with encryption := construct c base i} ∧
    EncryptionSem c {base with encryption := construct c base i} :=
  ⟨canonical_witness_preserved c base i baseCanonical cryptoCanonical,
    constructed_encryption_semantics c base i⟩

def replaceTier (base : TransferSem.Witness) (slot : Fin 4) (tier : Tier) : TransferSem.Witness :=
  {base with encryption := {base.encryption with tiers :=
    fun j => if j = slot then tier else base.encryption.tiers j}}

theorem refuse_timestamp_mutation (c : Crypto) (base : TransferSem.Witness) (bad : Nat)
    (changed : bad ≠ base.timestamp) :
    ¬ EncryptionSem c {base with encryption := {base.encryption with timestamp := bad}} := by
  intro invalid
  exact changed invalid.2.1

theorem refuse_epoch_mutation (c : Crypto) (base : TransferSem.Witness) (bad : Nat)
    (changed : bad ≠ (if base.regulated then base.registry.audit.epoch else 0)) :
    ¬ EncryptionSem c {base with encryption := {base.encryption with auditEpoch := bad}} := by
  intro invalid
  exact changed invalid.2.2.1

theorem refuse_salt_mutation (c : Crypto) (base : TransferSem.Witness) (slot : Fin 4) (bad : Nat)
    (changed : bad ≠ salt c base (slot.val+1)) :
    ¬ EncryptionSem c {base with encryption := {base.encryption with salts :=
      (fun j => if j = slot then bad else base.encryption.salts j)}} := by
  intro invalid
  have equation := invalid.2.2.2.2.1 slot
  simp only at equation
  exact changed equation

theorem refuse_core_confirmation_mutation (c : Crypto) (base : TransferSem.Witness)
    (slot : Fin 4) (core : slot.val = 0 ∨ slot.val = 2) (bad : Nat)
    (changed : bad ≠ c.hash .keyConfirmation
      ([fsub (base.encryption.tiers slot).c2
        (secret c (c.mul (base.encryption.tiers slot).ephemeral (selectedKey c base)))] ++
        pointFields (base.encryption.tiers slot).epk ++ [salt c base (slot.val+1)])) :
    ¬ EncryptionSem c (replaceTier base slot {base.encryption.tiers slot with confirmation := bad}) := by
  intro invalid
  have equations := (invalid.2.2.2.2.2.2.1 slot).2.2.2
  rw [if_pos core] at equations
  have equation := equations.1
  simp only [replaceTier] at equation
  exact changed equation

theorem refuse_core_ciphertext_mutation (c : Crypto) (base : TransferSem.Witness)
    (slot : Fin 4) (core : slot.val = 0 ∨ slot.val = 2) (bad : Nat)
    (changed : bad ≠ fadd (base.outputs 0).amount
      (stream c (fsub (base.encryption.tiers slot).c2
        (secret c (c.mul (base.encryption.tiers slot).ephemeral (selectedKey c base)))) 0)) :
    ¬ EncryptionSem c (replaceTier base slot {base.encryption.tiers slot with ciphertext :=
      fun j => if j.val = 0 then bad else (base.encryption.tiers slot).ciphertext j}) := by
  intro invalid
  have equations := (invalid.2.2.2.2.2.2.1 slot).2.2.2
  rw [if_pos core] at equations
  have equation := equations.2
  simp only [replaceTier] at equation
  exact changed equation

theorem refuse_extended_ciphertext_mutation (c : Crypto) (base : TransferSem.Witness)
    (slot : Fin 4) (extended : ¬(slot.val = 0 ∨ slot.val = 2)) (j : Fin 3) (bad : Nat)
    (changed : bad ≠ fadd
      (c.addressWords (if slot.val = 1 then base.receiver.address else base.sender.address) j)
      (stream c (fsub (base.encryption.tiers slot).c2
        (secret c (c.mul (base.encryption.tiers slot).ephemeral (selectedKey c base)))) j.val)) :
    ¬ EncryptionSem c (replaceTier base slot {base.encryption.tiers slot with ciphertext :=
      (fun k => if k = j then bad else (base.encryption.tiers slot).ciphertext k)}) := by
  intro invalid
  have equations := (invalid.2.2.2.2.2.2.1 slot).2.2.2
  rw [if_neg extended] at equations
  have equation := equations j
  simp only [replaceTier,ite_true] at equation
  exact changed equation

#print axioms fadd_canonical
#print axioms fsub_canonical
#print axioms fsub_fadd_cancel
#print axioms constructed_tier_seed
#print axioms constructed_tier_semantics
#print axioms constructed_encryption_semantics
#print axioms restore_full_record
#print axioms fieldsCanonical_append
#print axioms canonical_list_lookup
#print axioms canonical_constructed_ciphertext
#print axioms canonical_constructed_confirmation
#print axioms canonical_constructed_encryption_fields
#print axioms canonical_witness_preserved
#print axioms constructed_canonical_encryption_semantics
#print axioms refuse_timestamp_mutation
#print axioms refuse_epoch_mutation
#print axioms refuse_salt_mutation
#print axioms refuse_core_confirmation_mutation
#print axioms refuse_core_ciphertext_mutation
#print axioms refuse_extended_ciphertext_mutation
end ShielddSecurity.TransferEncryptionBranchCompletion
