import ShielddSecurity.RegistryNaturalSeed298
import ShielddSecurity.TransferSem
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeTransitionAlgebra831
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model

theorem facts (c : Crypto) (w : TransferSem.Witness) (volume : VolumeSem c w) :
    ((if w.volume.useReal then (1:F) else 0)*(1-(if eligible w then 1 else 0))=0) ∧
    ((if w.volume.useReal then (1:F) else 0)*(-((w.outputs 0).amount:F)+(-(w.volume.prior:F)+(w.volume.successor:F)))=0) ∧
    (((if w.volume.useReal then (1:F) else 0)*(if w.volume.startsNewDay then 1 else 0))*(w.volume.prior:F)=0) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,realSem,_,_⟩ := volume
  cases real : w.volume.useReal
  · simp
  · have allowed := realSem real
    constructor
    · simp only [allowed.1,if_true,sub_self,mul_zero]
    constructor
    · rw [allowed.2.2.1]
      simp only [if_true,Nat.cast_add]
      ring
    · cases starts : w.volume.startsNewDay
      · simp
      · have zero : w.volume.prior=0 := by simpa only [starts,if_true] using allowed.2.2.2.2
        simp only [if_true,zero,Nat.cast_zero,mul_zero]
end ShielddSecurity.VolumeTransitionAlgebra831

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionAlgebra831.facts
#print axioms ShielddSecurity.VolumeTransitionAlgebra831.facts
