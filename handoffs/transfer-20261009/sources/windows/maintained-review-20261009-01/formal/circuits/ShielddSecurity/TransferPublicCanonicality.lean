import ShielddSecurity.TransferSemanticStatementCompletion

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferPublicCanonicality
open TransferSem TransferCore

theorem fieldsCanonical_append (a b : List Nat) :
    fieldsCanonical (a ++ b) ↔ fieldsCanonical a ∧ fieldsCanonical b := by
  simp only [fieldsCanonical,List.mem_append,or_imp,forall_and]

theorem canonical_fin_block {n : Nat} (blocks : Fin n → List Nat)
    (canonical : fieldsCanonical ((List.finRange n).flatMap blocks)) (slot : Fin n) :
    fieldsCanonical (blocks slot) := by
  intro value member
  exact canonical value (List.mem_flatMap.mpr ⟨slot,by simp,member⟩)

theorem canonical_fin_map {n : Nat} (fields : Fin n → Nat)
    (canonical : fieldsCanonical ((List.finRange n).map fields)) (slot : Fin n) :
    fields slot < fieldModulus :=
  canonical _ (List.mem_map.mpr ⟨slot,by simp,rfl⟩)

theorem canonical_spend_output_inventory (w : TransferSem.Witness)
    (canonical : CanonicalWitness w) (slot : Fin 2) :
    fieldsCanonical (spendFields (w.spends slot)) ∧ fieldsCanonical (outputFields (w.outputs slot)) := by
  simp only [CanonicalWitness,fieldsCanonical_append] at canonical
  have block := canonical_fin_block _ canonical.1.1.2 slot
  exact (fieldsCanonical_append _ _).mp block

theorem canonical_tier_inventory (w : TransferSem.Witness)
    (canonical : CanonicalWitness w) (slot : Fin 4) :
    fieldsCanonical [w.encryption.detection slot,w.encryption.policy slot,w.encryption.salts slot,
      (w.encryption.tiers slot).ephemeral,(w.encryption.tiers slot).c2,
      (w.encryption.tiers slot).confirmation] ∧
    CanonicalAffine (w.encryption.tiers slot).epk ∧
    ∀ j : Fin 3, (w.encryption.tiers slot).ciphertext j < fieldModulus := by
  have encryption := canonical
  simp only [CanonicalWitness,fieldsCanonical_append] at encryption
  have fields := encryption.2
  simp only [encryptionFields,fieldsCanonical_append] at fields
  have tier := canonical_fin_block _ fields.1.1 slot
  simp only [fieldsCanonical_append] at tier
  have point := tier.1.2
  simp only [pointFields,fieldsCanonical,List.mem_cons,List.not_mem_nil,
    forall_eq_or_imp,false_implies,forall_const,and_true] at point
  exact ⟨tier.1.1,point,canonical_fin_map _ tier.2⟩

theorem canonical_ownership_inventory (w : TransferSem.Witness)
    (canonical : CanonicalWitness w) (slot : Fin 2) :
    (w.encryption.ownership slot).randomness < fieldModulus ∧
    CanonicalAffine (w.encryption.ownership slot).r ∧ CanonicalAffine (w.encryption.ownership slot).c := by
  have encryption := canonical
  simp only [CanonicalWitness,fieldsCanonical_append] at encryption
  have fields := encryption.2
  simp only [encryptionFields,fieldsCanonical_append] at fields
  have ownership := canonical_fin_block _ fields.2 slot
  simp only [fieldsCanonical_append] at ownership
  have randomness := ownership.1.1
  have r := ownership.1.2
  have c := ownership.2
  simp only [pointFields,fieldsCanonical,List.mem_cons,List.not_mem_nil,
    forall_eq_or_imp,false_implies,forall_const,and_true] at randomness r c
  exact ⟨randomness,r,c⟩

theorem canonical_balance (c : Crypto) (w : TransferSem.Witness) (crypto : CanonicalCrypto c) :
    CanonicalAffine (balance c w) :=
  crypto.2.2.2.1 _ _

theorem canonical_public_fields (c : Crypto) (w : TransferSem.Witness)
    (canonical : CanonicalWitness w) (crypto : CanonicalCrypto c) :
    fieldsCanonical (publicFields c w) := by
  have note0 := canonical_spend_output_inventory w canonical 0
  have note1 := canonical_spend_output_inventory w canonical 1
  have tier0 := canonical_tier_inventory w canonical 0
  have tier1 := canonical_tier_inventory w canonical 1
  have tier2 := canonical_tier_inventory w canonical 2
  have tier3 := canonical_tier_inventory w canonical 3
  have ownership0 := canonical_ownership_inventory w canonical 0
  have ownership1 := canonical_ownership_inventory w canonical 1
  have net := canonical_balance c w crypto
  have base := canonical
  simp only [CanonicalWitness,fieldsCanonical_append] at base
  rcases base with
    ⟨⟨⟨⟨⟨⟨⟨⟨header,_ak⟩,rk⟩,_registry⟩,_sender⟩,_receiver⟩,_notes⟩,volume⟩,encryption⟩
  have metadata := encryption
  simp only [encryptionFields,fieldsCanonical_append] at metadata
  simp only [publicFields,fieldsCanonical,List.mem_cons,List.not_mem_nil,
    forall_eq_or_imp,false_implies,forall_const,and_true]
  repeat' apply And.intro
  all_goals solve
    | exact net.1
    | exact net.2
    | exact ownership0.2.1.1
    | exact ownership0.2.1.2
    | exact ownership0.2.2.1
    | exact ownership0.2.2.2
    | exact ownership1.2.1.1
    | exact ownership1.2.1.2
    | exact ownership1.2.2.1
    | exact ownership1.2.2.2
    | exact tier0.2.1.1
    | exact tier0.2.1.2
    | exact tier1.2.1.1
    | exact tier1.2.1.2
    | exact tier2.2.1.1
    | exact tier2.2.1.2
    | exact tier3.2.1.1
    | exact tier3.2.1.2
    | exact tier0.2.2 0
    | exact tier1.2.2 0
    | exact tier1.2.2 1
    | exact tier1.2.2 2
    | exact tier2.2.2 0
    | exact tier3.2.2 0
    | exact tier3.2.2 1
    | exact tier3.2.2 2
    | apply header; simp
    | apply rk; simp [pointFields]
    | apply volume; simp [volumeFields]
    | apply note0.1; simp [spendFields]
    | apply note1.1; simp [spendFields]
    | apply note0.2; simp [outputFields,recoveryFields,pointFields]
    | apply note1.2; simp [outputFields,recoveryFields,pointFields]
    | apply tier0.1; simp
    | apply tier1.1; simp
    | apply tier2.1; simp
    | apply tier3.1; simp
    | apply metadata.1.2; simp

theorem transfer_sem_of_components (c : Crypto) (w : TransferSem.Witness)
    (canonical : CanonicalWitness w) (crypto : CanonicalCrypto c) (components : ComponentsSem c w) :
    TransferSem.TransferSem c w :=
  ⟨canonical,components,canonical_public_fields c w canonical crypto⟩

theorem source_public_canonical (c : Crypto) (w : TransferSem.Witness)
    (canonical : CanonicalWitness w) (crypto : CanonicalCrypto c) :
    fieldsCanonical (TransferNativeStatementSequence.rustFields
      (TransferSemanticStatementCompletion.nativeSource c w)) := by
  rw [TransferSemanticStatementCompletion.source_public_fields]
  exact canonical_public_fields c w canonical crypto

theorem source_full64_from_canonical {F Sdk Raw Encoded : Type} [Field F] [CharP F Scalar.modulus]
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (sdk : TransferNativeFieldBridge.SdkEncoder Sdk F)
    (numeric : TransferSemanticStatementCompletion.SdkNatConstructor Sdk F sdk)
    (c : Crypto) (w : TransferSem.Witness) (canonical : CanonicalWitness w) (crypto : CanonicalCrypto c) :
    ∃ outputs, TransferNativeFieldBridge.fields operations primitives sdk
        ((publicFields c w).map numeric.ofNat) = some outputs ∧
      outputs.map (ShielddNativeScalar.value operations) =
        (publicFields c w).map (fun n => (n : F)) ∧ outputs.length = 64 := by
  obtain ⟨outputs,read,meaning,count⟩ :=
    TransferNativeStatementSequence.source_sequence_conversion operations primitives sdk
      (TransferSemanticStatementCompletion.mapSource numeric.ofNat
        (TransferSemanticStatementCompletion.nativeSource c w))
  rw [TransferSemanticStatementCompletion.mapped_source_fields,
    TransferSemanticStatementCompletion.source_public_fields] at read meaning
  refine ⟨outputs,read,?_,count⟩
  rw [meaning,List.map_map]
  apply List.map_congr_left
  intro n member
  exact numeric.value n (canonical_public_fields c w canonical crypto n member)

-- Controls expose why both independent codomain premises are needed. They do
-- not assert that the deployed Rust crypto has these interpretations.
theorem noncanonical_anchor_control (c : Crypto) (w : TransferSem.Witness) :
    ¬ fieldsCanonical (publicFields c {w with anchor := fieldModulus}) := by
  intro canonical
  exact Nat.lt_irrefl fieldModulus (canonical fieldModulus (by simp [publicFields]))

def overflowingAdd (c : Crypto) : Crypto :=
  {c with add := fun _ _ => {x := fieldModulus,y := 0}}

theorem missing_crypto_codomain_control (c : Crypto) (w : TransferSem.Witness) :
    ¬ fieldsCanonical (publicFields (overflowingAdd c) w) := by
  intro canonical
  have member : fieldModulus ∈ publicFields (overflowingAdd c) w := by
    simp [publicFields,balance,overflowingAdd]
  exact Nat.lt_irrefl fieldModulus (canonical fieldModulus member)

#print axioms fieldsCanonical_append
#print axioms canonical_fin_block
#print axioms canonical_fin_map
#print axioms canonical_spend_output_inventory
#print axioms canonical_tier_inventory
#print axioms canonical_ownership_inventory
#print axioms canonical_balance
#print axioms canonical_public_fields
#print axioms transfer_sem_of_components
#print axioms source_public_canonical
#print axioms source_full64_from_canonical
#print axioms noncanonical_anchor_control
#print axioms missing_crypto_codomain_control
end ShielddSecurity.TransferPublicCanonicality
