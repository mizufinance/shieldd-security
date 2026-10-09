import ShielddSecurity.TransferSem

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferOutputRecoveryCompletion
open TransferSem TransferCore

structure RawOutputInputs where
  amount : Nat
  blinding : Nat
  seed : Nat
  salt : Nat
  randomizer : Nat

structure LegalOutputInputs (c : Crypto) where
  raw : Fin 2 → RawOutputInputs
  amountBounded : ∀ slot, (raw slot).amount < amountBound
  recipientNonzero : (raw 0).amount ≠ 0
  randomizerBounded : ∀ slot, (raw slot).randomizer < scalarOrder
  epkNonidentity : ∀ slot, nonidentity (c.mul (raw slot).randomizer c.generator)

def constructRecovery (c : Crypto) (base : TransferSem.Witness) (i : RawOutputInputs) : Recovery :=
  let epk := c.mul i.randomizer c.generator
  let c2 := fadd i.seed (secret c (c.mul i.randomizer (payloadKey c base)))
  let confirmation := c.hash .recoveryConfirmation ([i.seed] ++ pointFields epk ++ [i.salt])
  let encryptedAmount := fadd i.amount (stream c i.seed 0)
  let encryptedBlinding := fadd i.blinding (stream c i.seed 1)
  { epk := epk, c2 := c2, salt := i.salt, confirmation := confirmation,
    encryptedAmount := encryptedAmount, encryptedBlinding := encryptedBlinding,
    commitment := c.hash .recoveryCommitment (pointFields epk ++
      [c2,i.salt,confirmation,encryptedAmount,encryptedBlinding]),
    seed := i.seed, randomizer := i.randomizer }

def constructOutput (c : Crypto) (base : TransferSem.Witness) (slot : Fin 2)
    (i : RawOutputInputs) : Output :=
  let recovery := constructRecovery c base i
  { amount := i.amount, blinding := i.blinding, recovery := recovery,
    noteCommitment := noteCommitment c base.asset
      (if slot.val = 0 then base.receiver.address else base.sender.address)
      i.blinding i.amount recovery.commitment }

def constructOutputs (c : Crypto) (base : TransferSem.Witness) (i : LegalOutputInputs c) : Fin 2 → Output :=
  fun slot => constructOutput c base slot (i.raw slot)

theorem constructed_output_semantics (c : Crypto) (base : TransferSem.Witness)
    (i : LegalOutputInputs c) :
    ∀ slot : Fin 2, OutputSem c {base with outputs := constructOutputs c base i} slot := by
  intro slot
  have nonzero : slot.val = 0 → (i.raw slot).amount ≠ 0 := by
    intro h
    have eq : slot = 0 := Fin.ext h
    simpa only [eq] using i.recipientNonzero
  exact ⟨i.amountBounded slot, nonzero, rfl, i.randomizerBounded slot, rfl,
    i.epkNonidentity slot, rfl, rfl, rfl, rfl, rfl⟩

theorem restore_full_record (c : Crypto) (base : TransferSem.Witness) (i : LegalOutputInputs c) :
    {{base with outputs := constructOutputs c base i} with outputs := base.outputs} = base := by
  cases base
  rfl

theorem fadd_canonical (a b : Nat) : fadd a b < fieldModulus :=
  Nat.mod_lt _ (by decide)

theorem canonical_constructed_recovery (c : Crypto) (base : TransferSem.Witness)
    (i : RawOutputInputs) (cryptoCanonical : CanonicalCrypto c)
    (randomizerBounded : i.randomizer < scalarOrder)
    (seedCanonical : i.seed < fieldModulus) (saltCanonical : i.salt < fieldModulus) :
    fieldsCanonical (recoveryFields (constructRecovery c base i)) := by
  have scalarField : scalarOrder < fieldModulus := by decide
  have epk := cryptoCanonical.2.2.1 i.randomizer c.generator
  simp only [constructRecovery,recoveryFields,pointFields,fieldsCanonical,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_imp,forall_and,
    forall_eq,false_implies,and_true]
  exact ⟨⟨epk.1,epk.2⟩,fadd_canonical _ _,saltCanonical,cryptoCanonical.1 _ _,
    fadd_canonical _ _,fadd_canonical _ _,cryptoCanonical.1 _ _,seedCanonical,
    Nat.lt_trans randomizerBounded scalarField⟩

theorem fieldsCanonical_append (a b : List Nat) :
    fieldsCanonical (a ++ b) ↔ fieldsCanonical a ∧ fieldsCanonical b := by
  simp only [fieldsCanonical,List.mem_append,or_imp,forall_and]

theorem canonical_constructed_output (c : Crypto) (base : TransferSem.Witness)
    (i : LegalOutputInputs c) (slot : Fin 2) (cryptoCanonical : CanonicalCrypto c)
    (blindingCanonical : (i.raw slot).blinding < fieldModulus)
    (seedCanonical : (i.raw slot).seed < fieldModulus)
    (saltCanonical : (i.raw slot).salt < fieldModulus) :
    fieldsCanonical (outputFields (constructOutputs c base i slot)) := by
  have amountField : amountBound < fieldModulus := by decide
  rw [outputFields,fieldsCanonical_append]
  constructor
  · simp only [constructOutputs,constructOutput,fieldsCanonical,List.mem_cons,
      List.not_mem_nil,forall_eq_or_imp,false_implies,forall_const,and_true]
    exact ⟨blindingCanonical,Nat.lt_trans (i.amountBounded slot) amountField,cryptoCanonical.1 _ _⟩
  · exact canonical_constructed_recovery c base (i.raw slot) cryptoCanonical
      (i.randomizerBounded slot) seedCanonical saltCanonical

theorem canonical_witness_preserved (c : Crypto) (base : TransferSem.Witness)
    (i : LegalOutputInputs c) (baseCanonical : CanonicalWitness base)
    (cryptoCanonical : CanonicalCrypto c)
    (blindingCanonical : ∀ slot, (i.raw slot).blinding < fieldModulus)
    (seedCanonical : ∀ slot, (i.raw slot).seed < fieldModulus)
    (saltCanonical : ∀ slot, (i.raw slot).salt < fieldModulus) :
    CanonicalWitness {base with outputs := constructOutputs c base i} := by
  simp only [CanonicalWitness,fieldsCanonical_append] at baseCanonical ⊢
  rcases baseCanonical with
    ⟨⟨⟨⟨⟨⟨⟨⟨header,ak⟩,rk⟩,registry⟩,sender⟩,receiver⟩,notes⟩,volume⟩,encryption⟩
  have newNotes : fieldsCanonical ((List.finRange 2).flatMap
      (fun slot => spendFields (base.spends slot) ++ outputFields (constructOutputs c base i slot))) := by
    intro value member
    rcases List.mem_flatMap.mp member with ⟨slot,slotMem,valueMem⟩
    rcases List.mem_append.mp valueMem with spendMem | outputMem
    · exact notes value (List.mem_flatMap.mpr ⟨slot,slotMem,List.mem_append.mpr (Or.inl spendMem)⟩)
    · exact canonical_constructed_output c base i slot cryptoCanonical
        (blindingCanonical slot) (seedCanonical slot) (saltCanonical slot) value outputMem
  exact ⟨⟨⟨⟨⟨⟨⟨⟨header,ak⟩,rk⟩,registry⟩,sender⟩,receiver⟩,newNotes⟩,volume⟩,encryption⟩

theorem constructed_canonical_output_semantics (c : Crypto) (base : TransferSem.Witness)
    (i : LegalOutputInputs c) (baseCanonical : CanonicalWitness base)
    (cryptoCanonical : CanonicalCrypto c)
    (blindingCanonical : ∀ slot, (i.raw slot).blinding < fieldModulus)
    (seedCanonical : ∀ slot, (i.raw slot).seed < fieldModulus)
    (saltCanonical : ∀ slot, (i.raw slot).salt < fieldModulus) :
    CanonicalWitness {base with outputs := constructOutputs c base i} ∧
    ∀ slot : Fin 2, OutputSem c {base with outputs := constructOutputs c base i} slot :=
  ⟨canonical_witness_preserved c base i baseCanonical cryptoCanonical
    blindingCanonical seedCanonical saltCanonical, constructed_output_semantics c base i⟩

def replaceOutput (base : TransferSem.Witness) (slot : Fin 2) (o : Output) : TransferSem.Witness :=
  {base with outputs := fun j => if j = slot then o else base.outputs j}

theorem refuse_oversized_amount (c : Crypto) (base : TransferSem.Witness)
    (slot : Fin 2) (bad : Output) (oversized : amountBound ≤ bad.amount) :
    ¬ OutputSem c (replaceOutput base slot bad) slot := by
  intro invalid
  have bound := invalid.1
  simp only [replaceOutput] at bound
  exact Nat.not_lt_of_ge oversized bound

theorem refuse_zero_recipient (c : Crypto) (base : TransferSem.Witness)
    (bad : Output) (zero : bad.amount = 0) :
    ¬ OutputSem c (replaceOutput base 0 bad) 0 := by
  intro invalid
  have nonzero := invalid.2.1 rfl
  simp only [replaceOutput] at nonzero
  exact nonzero zero

theorem refuse_oversized_randomizer (c : Crypto) (base : TransferSem.Witness)
    (slot : Fin 2) (bad : Output) (oversized : scalarOrder ≤ bad.recovery.randomizer) :
    ¬ OutputSem c (replaceOutput base slot bad) slot := by
  intro invalid
  have bound := invalid.2.2.2.1
  simp only [replaceOutput] at bound
  exact Nat.not_lt_of_ge oversized bound

theorem refuse_confirmation_mutation (c : Crypto) (base : TransferSem.Witness)
    (slot : Fin 2) (bad : Output)
    (changed : bad.recovery.confirmation ≠ c.hash .recoveryConfirmation
      ([bad.recovery.seed] ++ pointFields bad.recovery.epk ++ [bad.recovery.salt])) :
    ¬ OutputSem c (replaceOutput base slot bad) slot := by
  intro invalid
  have equation := invalid.2.2.2.2.2.2.2.1
  simp only [replaceOutput] at equation
  exact changed equation

theorem refuse_recovery_commitment_mutation (c : Crypto) (base : TransferSem.Witness)
    (slot : Fin 2) (bad : Output)
    (changed : bad.recovery.commitment ≠ c.hash .recoveryCommitment
      (pointFields bad.recovery.epk ++ [bad.recovery.c2,bad.recovery.salt,
        bad.recovery.confirmation,bad.recovery.encryptedAmount,bad.recovery.encryptedBlinding])) :
    ¬ OutputSem c (replaceOutput base slot bad) slot := by
  intro invalid
  have equation := invalid.2.2.2.2.2.2.2.2.2.2
  simp only [replaceOutput] at equation
  exact changed equation

theorem refuse_note_commitment_mutation (c : Crypto) (base : TransferSem.Witness)
    (slot : Fin 2) (bad : Output)
    (changed : bad.noteCommitment ≠ noteCommitment c base.asset
      (if slot.val = 0 then base.receiver.address else base.sender.address)
      bad.blinding bad.amount bad.recovery.commitment) :
    ¬ OutputSem c (replaceOutput base slot bad) slot := by
  intro invalid
  have equation := invalid.2.2.1
  simp only [replaceOutput] at equation
  exact changed equation

#print axioms constructed_output_semantics
#print axioms restore_full_record
#print axioms fadd_canonical
#print axioms canonical_constructed_recovery
#print axioms fieldsCanonical_append
#print axioms canonical_constructed_output
#print axioms canonical_witness_preserved
#print axioms constructed_canonical_output_semantics
#print axioms refuse_oversized_amount
#print axioms refuse_zero_recipient
#print axioms refuse_oversized_randomizer
#print axioms refuse_confirmation_mutation
#print axioms refuse_recovery_commitment_mutation
#print axioms refuse_note_commitment_mutation
end ShielddSecurity.TransferOutputRecoveryCompletion
