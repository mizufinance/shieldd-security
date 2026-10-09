import ShielddSecurity.TransferSpendBranchCompletion

set_option maxHeartbeats 200000

/-! Recover raw spend inputs from each legal semantic slot, including the dummy
slot's inactive path data. SpendSem is consumed only in this inverse direction.
Authentication is transported from the original legal witness, while the
forward constructor computes each nullifier. Circuit rows remain separate. -/
namespace ShielddSecurity.TransferSpendDecomposition

open TransferCore TransferSem TransferSpendBranchCompletion

def recoverRaw (w : TransferSem.Witness) (slot : Fin 2) : RawSpend :=
  let s := w.spends slot
  ⟨s.blinding, s.amount, s.recovery, s.position, s.siblings⟩

theorem recovered_raw_fields (w : TransferSem.Witness) (slot : Fin 2) :
    (recoverRaw w slot).blinding = (w.spends slot).blinding ∧
    (recoverRaw w slot).amount = (w.spends slot).amount ∧
    (recoverRaw w slot).recovery = (w.spends slot).recovery ∧
    (recoverRaw w slot).position = (w.spends slot).position ∧
    (recoverRaw w slot).siblings = (w.spends slot).siblings :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem nullifier_recovered (c : Crypto) (w : TransferSem.Witness) (slot : Fin 2)
    (legal : SpendSem c w slot) :
    nullifier c w slot (recoverRaw w slot) = (w.spends slot).nullifier := by
  have branch := legal.2.2
  change (if isDummy w slot then
      (w.spends slot).amount = 0 ∧ (w.spends slot).nullifier =
        c.hash .dummyNullifier [w.paddingSeed, w.auth.randomizer, 1]
    else (w.spends slot).nullifier =
      c.hash .noteNullifier [effectiveNK c w, commitment c w (recoverRaw w slot),
        (w.spends slot).position] ∧
      root c .state (w.spends slot).position (commitment c w (recoverRaw w slot))
        (w.spends slot).siblings = w.anchor) at branch
  unfold nullifier
  by_cases dummy : isDummy w slot
  · rw [if_pos dummy] at branch ⊢
    exact branch.2.symm
  · rw [if_neg dummy] at branch ⊢
    exact branch.1.symm

theorem spend_reconstructed (c : Crypto) (w : TransferSem.Witness) (slot : Fin 2)
    (legal : SpendSem c w slot) :
    constructSpend c w slot (recoverRaw w slot) = w.spends slot := by
  unfold constructSpend
  rw [nullifier_recovered c w slot legal]
  cases w.spends slot
  rfl

def recoverInputs (c : Crypto) (w : TransferSem.Witness)
    (legal : ∀ slot, SpendSem c w slot)
    (canonical : ∀ slot, fieldsCanonical (spendFields (w.spends slot))) : LegalInputs c w where
  raw := recoverRaw w
  amountBounded := fun slot => (legal slot).1
  positionBounded := fun slot => (legal slot).2.1
  blindingCanonical := by
    intro slot
    apply canonical slot
    simp only [spendFields, List.mem_append, List.mem_cons, List.not_mem_nil]
    exact Or.inl (Or.inl rfl)
  recoveryCanonical := by
    intro slot
    apply canonical slot
    simp only [spendFields, List.mem_append, List.mem_cons, List.not_mem_nil]
    exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
  pathCanonical := fun slot =>
    (TransferSpendBranchCompletion.fieldsCanonical_append _ _).mp (canonical slot) |>.2
  dummyAmount := by
    intro slot dummy
    have branch := (legal slot).2.2
    change (if isDummy w slot then _ else _) at branch
    rw [if_pos dummy] at branch
    exact branch.1
  authenticated := by
    intro slot real
    have branch := (legal slot).2.2
    change (if isDummy w slot then _ else _) at branch
    rw [if_neg real] at branch
    exact branch.2

theorem recovered_inputs_raw (c : Crypto) (w : TransferSem.Witness)
    (legal : ∀ slot, SpendSem c w slot)
    (canonical : ∀ slot, fieldsCanonical (spendFields (w.spends slot))) (slot : Fin 2) :
    (recoverInputs c w legal canonical).raw slot = recoverRaw w slot := rfl

theorem full_record_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (legal : ∀ slot, SpendSem c w slot)
    (canonical : ∀ slot, fieldsCanonical (spendFields (w.spends slot))) :
    construct c w (recoverInputs c w legal canonical) = w := by
  have restored : (fun slot => constructSpend c w slot (recoverRaw w slot)) = w.spends := by
    funext slot
    exact spend_reconstructed c w slot (legal slot)
  change {w with spends := fun slot => constructSpend c w slot (recoverRaw w slot)} = w
  rw [restored]

set_option pp.all true in
#check @recovered_raw_fields
#print axioms recovered_raw_fields
set_option pp.all true in
#check @nullifier_recovered
#print axioms nullifier_recovered
set_option pp.all true in
#check @spend_reconstructed
#print axioms spend_reconstructed
set_option pp.all true in
#check @recovered_inputs_raw
#print axioms recovered_inputs_raw
set_option pp.all true in
#check @full_record_reconstructed
#print axioms full_record_reconstructed

end ShielddSecurity.TransferSpendDecomposition
