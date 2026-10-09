import ShielddSecurity.TransferOutputRecoveryCompletion

set_option maxHeartbeats 200000

/-! Inverse output/recovery construction on independent semantic witnesses.
The semantic equations justify recovering raw inputs; no output equation is
assumed by the forward constructor. This covers representation, not full rows
or a correspondence theorem for the Rust constructor. -/
namespace ShielddSecurity.TransferOutputDecomposition

open TransferCore TransferSem TransferOutputRecoveryCompletion

def recoverRaw (w : TransferSem.Witness) (slot : Fin 2) : RawOutputInputs :=
  let o := w.outputs slot
  ⟨o.amount, o.blinding, o.recovery.seed, o.recovery.salt, o.recovery.randomizer⟩

theorem recovered_raw_fields (w : TransferSem.Witness) (slot : Fin 2) :
    (recoverRaw w slot).amount = (w.outputs slot).amount ∧
    (recoverRaw w slot).blinding = (w.outputs slot).blinding ∧
    (recoverRaw w slot).seed = (w.outputs slot).recovery.seed ∧
    (recoverRaw w slot).salt = (w.outputs slot).recovery.salt ∧
    (recoverRaw w slot).randomizer = (w.outputs slot).recovery.randomizer :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem recovery_reconstructed (c : Crypto) (w : TransferSem.Witness) (slot : Fin 2)
    (legal : OutputSem c w slot) :
    constructRecovery c w (recoverRaw w slot) = (w.outputs slot).recovery := by
  rcases legal with ⟨_, _, _, _, point, _, masked, confirmation, amount, blinding, commitment⟩
  unfold constructRecovery recoverRaw
  dsimp only
  rw [← point, ← masked, ← confirmation, ← amount, ← blinding, ← commitment]
  cases (w.outputs slot).recovery
  rfl

theorem output_reconstructed (c : Crypto) (w : TransferSem.Witness) (slot : Fin 2)
    (legal : OutputSem c w slot) :
    constructOutput c w slot (recoverRaw w slot) = w.outputs slot := by
  have note := legal.2.2.1
  unfold constructOutput
  rw [recovery_reconstructed c w slot legal]
  change {blinding := (w.outputs slot).blinding, amount := (w.outputs slot).amount,
    recovery := (w.outputs slot).recovery,
    noteCommitment := noteCommitment c w.asset
      (if slot.val = 0 then w.receiver.address else w.sender.address)
      (w.outputs slot).blinding (w.outputs slot).amount (w.outputs slot).recovery.commitment} =
    w.outputs slot
  rw [← note]

def recoverInputs (c : Crypto) (w : TransferSem.Witness)
    (legal : ∀ slot, OutputSem c w slot) : LegalOutputInputs c where
  raw := recoverRaw w
  amountBounded := fun slot => (legal slot).1
  recipientNonzero := (legal 0).2.1 rfl
  randomizerBounded := fun slot => (legal slot).2.2.2.1
  epkNonidentity := by
    intro slot
    have point := (legal slot).2.2.2.2.1
    have nonzero := (legal slot).2.2.2.2.2.1
    change nonidentity (c.mul (w.outputs slot).recovery.randomizer c.generator)
    rw [← point]
    exact nonzero

theorem outputs_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (legal : ∀ slot, OutputSem c w slot) :
    constructOutputs c w (recoverInputs c w legal) = w.outputs := by
  funext slot
  exact output_reconstructed c w slot (legal slot)

theorem full_record_reconstructed (c : Crypto) (w : TransferSem.Witness)
    (legal : ∀ slot, OutputSem c w slot) :
    {w with outputs := constructOutputs c w (recoverInputs c w legal)} = w := by
  rw [outputs_reconstructed c w legal]

set_option pp.all true in
#check @recovered_raw_fields
#print axioms recovered_raw_fields
set_option pp.all true in
#check @recovery_reconstructed
#print axioms recovery_reconstructed
set_option pp.all true in
#check @output_reconstructed
#print axioms output_reconstructed
set_option pp.all true in
#check @outputs_reconstructed
#print axioms outputs_reconstructed
set_option pp.all true in
#check @full_record_reconstructed
#print axioms full_record_reconstructed

end ShielddSecurity.TransferOutputDecomposition
