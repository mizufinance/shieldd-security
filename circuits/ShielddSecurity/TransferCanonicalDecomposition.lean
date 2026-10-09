import ShielddSecurity.TransferSem

set_option maxHeartbeats 150000

/-! Project canonical storage facts from the independent complete witness
predicate. These bounds discharge the representation prerequisites of raw
inverse constructors. They do not establish circuit satisfaction. -/
namespace ShielddSecurity.TransferCanonicalDecomposition

open TransferCore TransferSem

private theorem canonical_append (left right : List Nat) :
    fieldsCanonical (left ++ right) ↔ fieldsCanonical left ∧ fieldsCanonical right := by
  simp only [fieldsCanonical, List.mem_append, or_imp, forall_and]

theorem authorization_scalars_canonical (w : TransferSem.Witness) (canonical : CanonicalWitness w) :
    w.auth.nk < fieldModulus ∧ w.auth.ivk < fieldModulus ∧
      w.auth.quotient < fieldModulus ∧ w.auth.randomizer < fieldModulus := by
  simp only [CanonicalWitness, canonical_append] at canonical
  rcases canonical with
    ⟨⟨⟨⟨⟨⟨⟨⟨header, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩
  exact ⟨header _ (by simp), header _ (by simp), header _ (by simp), header _ (by simp)⟩

theorem registry_fields_canonical (w : TransferSem.Witness) (canonical : CanonicalWitness w) :
    fieldsCanonical (registryFields w.registry) := by
  simp only [CanonicalWitness, canonical_append] at canonical
  rcases canonical with
    ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, registry⟩, _⟩, _⟩, _⟩, _⟩, _⟩
  exact registry

theorem user_fields_canonical (w : TransferSem.Witness) (canonical : CanonicalWitness w) :
    fieldsCanonical (userFields w.sender) ∧ fieldsCanonical (userFields w.receiver) := by
  simp only [CanonicalWitness, canonical_append] at canonical
  rcases canonical with
    ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, sender⟩, receiver⟩, _⟩, _⟩, _⟩
  exact ⟨sender, receiver⟩

theorem note_fields_canonical (w : TransferSem.Witness) (canonical : CanonicalWitness w) :
    ∀ slot : Fin 2, fieldsCanonical (spendFields (w.spends slot)) ∧
      fieldsCanonical (outputFields (w.outputs slot)) := by
  simp only [CanonicalWitness, canonical_append] at canonical
  rcases canonical with
    ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, notes⟩, _⟩, _⟩
  intro slot
  apply (canonical_append _ _).mp
  intro value member
  exact notes value (List.mem_flatMap.mpr ⟨slot, by simp, member⟩)

theorem volume_encryption_fields_canonical (w : TransferSem.Witness)
    (canonical : CanonicalWitness w) :
    fieldsCanonical (volumeFields w.volume) ∧ fieldsCanonical (encryptionFields w.encryption) := by
  simp only [CanonicalWitness, canonical_append] at canonical
  rcases canonical with ⟨beforeEncryption, encryption⟩
  exact ⟨beforeEncryption.2, encryption⟩

set_option pp.all true in
#check @authorization_scalars_canonical
#print axioms authorization_scalars_canonical
set_option pp.all true in
#check @registry_fields_canonical
#print axioms registry_fields_canonical
set_option pp.all true in
#check @user_fields_canonical
#print axioms user_fields_canonical
set_option pp.all true in
#check @note_fields_canonical
#print axioms note_fields_canonical
set_option pp.all true in
#check @volume_encryption_fields_canonical
#print axioms volume_encryption_fields_canonical

end ShielddSecurity.TransferCanonicalDecomposition
