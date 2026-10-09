import ShielddSecurity.TransferSem

set_option maxHeartbeats 200000

/-! Independent raw spend construction. Authenticated real-note membership is
an external legal-input law; nullifiers are computed, never supplied as desired
outputs. This component does not assert circuit-row or Rust correspondence. -/
namespace ShielddSecurity.TransferSpendBranchCompletion

open TransferCore TransferSem

structure RawSpend where
  blinding : Nat
  amount : Nat
  recovery : Nat
  position : Nat
  siblings : Path 24

def isDummy (base : TransferSem.Witness) (slot : Fin 2) : Prop :=
  slot.val = 1 ∧ base.optionalDummy = true

instance (base : TransferSem.Witness) (slot : Fin 2) : Decidable (isDummy base slot) :=
  inferInstanceAs (Decidable (slot.val = 1 ∧ base.optionalDummy = true))

def commitment (c : Crypto) (base : TransferSem.Witness) (raw : RawSpend) : Nat :=
  noteCommitment c base.asset base.sender.address raw.blinding raw.amount raw.recovery

structure LegalInputs (c : Crypto) (base : TransferSem.Witness) where
  raw : Fin 2 → RawSpend
  amountBounded : ∀ slot, (raw slot).amount < amountBound
  positionBounded : ∀ slot, (raw slot).position < 2 ^ 48
  blindingCanonical : ∀ slot, (raw slot).blinding < fieldModulus
  recoveryCanonical : ∀ slot, (raw slot).recovery < fieldModulus
  pathCanonical : ∀ slot, fieldsCanonical (pathFields (raw slot).siblings)
  dummyAmount : ∀ slot, isDummy base slot → (raw slot).amount = 0
  authenticated : ∀ slot, ¬ isDummy base slot →
    root c .state (raw slot).position (commitment c base (raw slot)) (raw slot).siblings = base.anchor

def nullifier (c : Crypto) (base : TransferSem.Witness) (slot : Fin 2) (raw : RawSpend) : Nat :=
  if isDummy base slot then c.hash .dummyNullifier [base.paddingSeed, base.auth.randomizer, 1]
  else c.hash .noteNullifier [effectiveNK c base, commitment c base raw, raw.position]

def constructSpend (c : Crypto) (base : TransferSem.Witness) (slot : Fin 2) (raw : RawSpend) : Spend :=
  ⟨raw.blinding, raw.amount, raw.recovery, raw.position, raw.siblings, nullifier c base slot raw⟩

def construct (c : Crypto) (base : TransferSem.Witness) (i : LegalInputs c base) : TransferSem.Witness :=
  {base with spends := fun slot => constructSpend c base slot (i.raw slot)}

theorem constructed_spend_semantics (c : Crypto) (base : TransferSem.Witness)
    (i : LegalInputs c base) : ∀ slot, SpendSem c (construct c base i) slot := by
  intro slot
  refine ⟨i.amountBounded slot, i.positionBounded slot, ?_⟩
  change if isDummy base slot then
    (i.raw slot).amount = 0 ∧ nullifier c base slot (i.raw slot) =
      c.hash .dummyNullifier [base.paddingSeed, base.auth.randomizer, 1]
    else nullifier c base slot (i.raw slot) =
      c.hash .noteNullifier [effectiveNK c base, commitment c base (i.raw slot), (i.raw slot).position] ∧
      root c .state (i.raw slot).position (commitment c base (i.raw slot)) (i.raw slot).siblings = base.anchor
  by_cases dummy : isDummy base slot
  · rw [if_pos dummy, nullifier, if_pos dummy]
    exact ⟨i.dummyAmount slot dummy, rfl⟩
  · rw [if_neg dummy, nullifier, if_neg dummy]
    exact ⟨rfl, i.authenticated slot dummy⟩

theorem required_slot_is_real (base : TransferSem.Witness) : ¬ isDummy base 0 := by
  simp only [isDummy, Fin.val_zero, Nat.zero_ne_one, false_and, not_false_eq_true]

theorem restore_full_record (c : Crypto) (base : TransferSem.Witness) (i : LegalInputs c base) :
    {construct c base i with spends := base.spends} = base := by
  cases base
  rfl

theorem raw_fields_preserved (c : Crypto) (base : TransferSem.Witness) (i : LegalInputs c base)
    (slot : Fin 2) :
    ((construct c base i).spends slot).blinding = (i.raw slot).blinding ∧
    ((construct c base i).spends slot).amount = (i.raw slot).amount ∧
    ((construct c base i).spends slot).recovery = (i.raw slot).recovery ∧
    ((construct c base i).spends slot).position = (i.raw slot).position ∧
    ((construct c base i).spends slot).siblings = (i.raw slot).siblings := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem nullifier_canonical (c : Crypto) (base : TransferSem.Witness) (slot : Fin 2)
    (raw : RawSpend) (cryptoCanonical : CanonicalCrypto c) :
    nullifier c base slot raw < fieldModulus := by
  unfold nullifier
  split <;> exact cryptoCanonical.1 _ _

theorem fieldsCanonical_append (a b : List Nat) :
    fieldsCanonical (a ++ b) ↔ fieldsCanonical a ∧ fieldsCanonical b := by
  simp only [fieldsCanonical, List.mem_append, or_imp, forall_and]

theorem constructed_spend_canonical (c : Crypto) (base : TransferSem.Witness)
    (i : LegalInputs c base) (slot : Fin 2) (cryptoCanonical : CanonicalCrypto c) :
    fieldsCanonical (spendFields (constructSpend c base slot (i.raw slot))) := by
  rw [spendFields, fieldsCanonical_append]
  constructor
  · simp only [constructSpend, fieldsCanonical, List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp, false_implies, forall_const, and_true]
    exact ⟨i.blindingCanonical slot,
      Nat.lt_trans (i.amountBounded slot) (by decide : amountBound < fieldModulus),
      i.recoveryCanonical slot,
      Nat.lt_trans (i.positionBounded slot) (by decide : 2 ^ 48 < fieldModulus),
      nullifier_canonical c base slot (i.raw slot) cryptoCanonical⟩
  · exact i.pathCanonical slot

theorem canonical_witness_preserved (c : Crypto) (base : TransferSem.Witness)
    (i : LegalInputs c base) (baseCanonical : CanonicalWitness base)
    (cryptoCanonical : CanonicalCrypto c) : CanonicalWitness (construct c base i) := by
  simp only [CanonicalWitness, fieldsCanonical_append] at baseCanonical ⊢
  rcases baseCanonical with
    ⟨⟨⟨⟨⟨⟨⟨⟨header, ak⟩, rk⟩, registry⟩, sender⟩, receiver⟩, notes⟩, volume⟩, encryption⟩
  have newNotes : fieldsCanonical ((List.finRange 2).flatMap
      (fun slot => spendFields (constructSpend c base slot (i.raw slot)) ++ outputFields (base.outputs slot))) := by
    intro value member
    rcases List.mem_flatMap.mp member with ⟨slot, slotMem, valueMem⟩
    rcases List.mem_append.mp valueMem with spendMem | outputMem
    · exact constructed_spend_canonical c base i slot cryptoCanonical value spendMem
    · exact notes value (List.mem_flatMap.mpr ⟨slot, slotMem, List.mem_append.mpr (Or.inr outputMem)⟩)
  exact ⟨⟨⟨⟨⟨⟨⟨⟨header, ak⟩, rk⟩, registry⟩, sender⟩, receiver⟩, newNotes⟩, volume⟩, encryption⟩

set_option pp.all true in
#check @constructed_spend_semantics
#print axioms constructed_spend_semantics
set_option pp.all true in
#check @required_slot_is_real
#print axioms required_slot_is_real
set_option pp.all true in
#check @restore_full_record
#print axioms restore_full_record
set_option pp.all true in
#check @raw_fields_preserved
#print axioms raw_fields_preserved
set_option pp.all true in
#check @nullifier_canonical
#print axioms nullifier_canonical
set_option pp.all true in
#check @fieldsCanonical_append
#print axioms fieldsCanonical_append
set_option pp.all true in
#check @constructed_spend_canonical
#print axioms constructed_spend_canonical
set_option pp.all true in
#check @canonical_witness_preserved
#print axioms canonical_witness_preserved

end ShielddSecurity.TransferSpendBranchCompletion
