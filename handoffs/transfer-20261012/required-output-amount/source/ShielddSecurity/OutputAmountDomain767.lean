import ShielddSecurity.RegistryNaturalSeed298
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OutputAmountDomain767
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

theorem amount_nonzero (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem c w) : ((w.outputs 0).amount:F)≠0 := by
  obtain ⟨_,_,_,_,_,outputs,_,_,_,_⟩ := legal.2.1
  have rules := outputs (0:Fin 2)
  have nonzero : (w.outputs 0).amount≠0 := rules.2.1 rfl
  have bound : (w.outputs 0).amount<TransferCore.fieldModulus := lt_trans rules.1 (by decide)
  have represented := RegistryNaturalSeed298.represented_nat (w.outputs 0).amount bound
  intro zero
  rw [zero] at represented
  change 0=(w.outputs 0).amount at represented
  exact nonzero represented.symm

def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column=4919 then ((w.outputs 0).amount:F)⁻¹ else original column

theorem selected (original : Nat → F) (w : TransferSem.Witness) :
    seed original w 4919=((w.outputs 0).amount:F)⁻¹ := by simp only [seed,if_pos rfl,if_true]

theorem inverse (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem c w) : seed original w 4919*((w.outputs 0).amount:F)=1 := by
  rw [selected]
  exact inv_mul_cancel₀ (amount_nonzero c w legal)
end ShielddSecurity.OutputAmountDomain767

set_option pp.all true in
#check @ShielddSecurity.OutputAmountDomain767.amount_nonzero
#print axioms ShielddSecurity.OutputAmountDomain767.amount_nonzero

set_option pp.all true in
#check @ShielddSecurity.OutputAmountDomain767.selected
#print axioms ShielddSecurity.OutputAmountDomain767.selected

set_option pp.all true in
#check @ShielddSecurity.OutputAmountDomain767.inverse
#print axioms ShielddSecurity.OutputAmountDomain767.inverse
