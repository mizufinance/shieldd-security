import ShielddSecurity.TierFlagSeed623
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierFlagSeedFacts665
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open TierFlagLayout620 (columns flags)
theorem seed_boolean (original : Nat → F) (w : TransferSem.Witness)
    (column : Nat) (member : column∈flags) :
    TierFlagSeed623.seed original w column=0 ∨ TierFlagSeed623.seed original w column=1 := by
  classical
  simp only [flags,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl
  · have value := TierFlagSeed623.flag original w ⟨0,by decide⟩
    change TierFlagSeed623.seed original w 7597=FieldZeroSeed125.flag (TierFlagSeed623.delta w ⟨0,by decide⟩) at value
    rw [value]
    unfold FieldZeroSeed125.flag
    split <;> simp
  · have value := TierFlagSeed623.flag original w ⟨1,by decide⟩
    change TierFlagSeed623.seed original w 7599=FieldZeroSeed125.flag (TierFlagSeed623.delta w ⟨1,by decide⟩) at value
    rw [value]
    unfold FieldZeroSeed125.flag
    split <;> simp
  · have value := TierFlagSeed623.flag original w ⟨2,by decide⟩
    change TierFlagSeed623.seed original w 7601=FieldZeroSeed125.flag (TierFlagSeed623.delta w ⟨2,by decide⟩) at value
    rw [value]
    unfold FieldZeroSeed125.flag
    split <;> simp
  · have value := TierFlagSeed623.flag original w ⟨3,by decide⟩
    change TierFlagSeed623.seed original w 7603=FieldZeroSeed125.flag (TierFlagSeed623.delta w ⟨3,by decide⟩) at value
    rw [value]
    unfold FieldZeroSeed125.flag
    split <;> simp
  · rw [(TierFlagSeed623.control_values original w).1]
    cases w.volume.useReal <;> simp
  · rw [(TierFlagSeed623.control_values original w).2.1]
    cases w.volume.startsNewDay <;> simp


theorem address_bounds (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem c w) (index : Fin 4) :
    TierFlagSeed623.left w index<TransferCore.fieldModulus ∧
    TierFlagSeed623.right w index<TransferCore.fieldModulus := by
  have sender := legal.2.1.2.1
  have receiver := legal.2.1.2.2.1
  fin_cases index
  · exact ⟨sender.1.1.1,receiver.1.1.1⟩
  · exact ⟨sender.1.1.2,receiver.1.1.2⟩
  · exact ⟨sender.2.2.1.1.1,receiver.2.2.1.1.1⟩
  · exact ⟨sender.2.2.1.1.2,receiver.2.2.1.1.2⟩

end ShielddSecurity.TierFlagSeedFacts665

set_option pp.all true in
#check @ShielddSecurity.TierFlagSeedFacts665.seed_boolean
#print axioms ShielddSecurity.TierFlagSeedFacts665.seed_boolean

set_option pp.all true in
#check @ShielddSecurity.TierFlagSeedFacts665.address_bounds
#print axioms ShielddSecurity.TierFlagSeedFacts665.address_bounds
