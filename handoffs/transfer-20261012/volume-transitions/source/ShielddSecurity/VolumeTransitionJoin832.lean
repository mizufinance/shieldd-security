import ShielddSecurity.VolumeTransitionBindings827
import ShielddSecurity.VolumeTransitionCapture828
import ShielddSecurity.VolumeTransitionAlgebra831
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeTransitionJoin832
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model

theorem rows (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness) (volume : VolumeSem c w)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (one : rho copy=1)
    (inputs : TierFlagMeaning619.Inputs rho w)
    (newDay : rho 7606=(if w.volume.startsNewDay then 1 else 0))
    (prior : rho 7741=(w.volume.prior:F)) (successor : rho 7742=(w.volume.successor:F))
    (outbound : rho 4789=((w.outputs 0).amount:F)) : VolumeTransitionCapture828.Rows rho := by
  have realValue := inputs.useReal
  have eligible := VolumeTransitionBindings827.eligible_value rho w arithmetic one inputs volume.2.2.2.2.1
  have e0 := VolumeTransitionCapture828.eligibility_equation rho arithmetic
  have e1 := VolumeTransitionCapture828.successor_equation rho arithmetic
  have e2 := VolumeTransitionCapture828.newDay_equation rho arithmetic
  have e3 := VolumeTransitionCapture828.prior_equation rho arithmetic
  simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at e0 e1 e2 e3
  have e0 : rho 108484=rho 7605*(rho copy-rho 108482) := by
    simpa only [copy,sub_eq_add_neg,add_comm] using e0
  rw [one,realValue,eligible] at e0
  rw [realValue,prior,successor,outbound] at e1
  rw [realValue,newDay] at e2
  rw [e2,prior] at e3
  have facts := VolumeTransitionAlgebra831.facts _ w volume
  apply VolumeTransitionCapture828.rows rho
  · exact e0.trans facts.1
  · exact e1.trans facts.2.1
  · exact e3.trans facts.2.2
end ShielddSecurity.VolumeTransitionJoin832

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionJoin832.rows
#print axioms ShielddSecurity.VolumeTransitionJoin832.rows
