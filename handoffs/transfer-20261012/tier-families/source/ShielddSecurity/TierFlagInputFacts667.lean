import ShielddSecurity.TierFlagSeedFacts665
import ShielddSecurity.TierFlagMeaning619
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierFlagInputFacts667
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

theorem inputs (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem c w) (rho : Nat → F)
    (regulated : rho 10=if w.regulated then 1 else 0)
    (frame : ∀ column, column∈TierFlagLayout620.columns → rho column=TierFlagSeed623.seed original w column) :
    TierFlagMeaning619.Inputs rho w := by
  have controls := TierFlagSeed623.control_values original w
  constructor
  · exact regulated
  · exact (frame 7607 (by decide +kernel)).trans controls.2.2
  · exact (frame 7605 (by decide +kernel)).trans controls.1
  · rw [frame 7597 (by decide +kernel)]
    have bounds := TierFlagSeedFacts665.address_bounds c w legal ⟨0,by decide⟩
    exact TierFlagSeed623.flag_meaning original w ⟨0,by decide⟩ bounds.1 bounds.2
  · rw [frame 7599 (by decide +kernel)]
    have bounds := TierFlagSeedFacts665.address_bounds c w legal ⟨1,by decide⟩
    exact TierFlagSeed623.flag_meaning original w ⟨1,by decide⟩ bounds.1 bounds.2
  · rw [frame 7601 (by decide +kernel)]
    have bounds := TierFlagSeedFacts665.address_bounds c w legal ⟨2,by decide⟩
    exact TierFlagSeed623.flag_meaning original w ⟨2,by decide⟩ bounds.1 bounds.2
  · rw [frame 7603 (by decide +kernel)]
    have bounds := TierFlagSeedFacts665.address_bounds c w legal ⟨3,by decide⟩
    exact TierFlagSeed623.flag_meaning original w ⟨3,by decide⟩ bounds.1 bounds.2

end ShielddSecurity.TierFlagInputFacts667
set_option pp.all true in
#check @ShielddSecurity.TierFlagInputFacts667.inputs
#print axioms ShielddSecurity.TierFlagInputFacts667.inputs
