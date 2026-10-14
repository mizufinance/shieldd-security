import ShielddSecurity.TierFlagCapture618
import ShielddSecurity.ConcreteJubjubField01
import ShielddSecurity.TransferSem
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierFlagMeaning619
open ConcreteJubjubField01 TransferCore TransferSem CompilerArithmeticTransport41 CompilerAssertionBlock51

theorem address_eq_iff (a b : Address) : a=b ↔
    a.diversified.x=b.diversified.x ∧ a.diversified.y=b.diversified.y ∧
    a.transmission.x=b.transmission.x ∧ a.transmission.y=b.transmission.y := by
  constructor
  · intro equal
    subst b
    exact ⟨rfl,rfl,rfl,rfl⟩
  · intro equal
    rcases a with ⟨⟨ax,ay⟩,⟨atx,aty⟩⟩
    rcases b with ⟨⟨bx,byCoord⟩,⟨btx,bty⟩⟩
    exact congrArg₂ Address.mk (congrArg₂ Affine.mk equal.1 equal.2.1)
      (congrArg₂ Affine.mk equal.2.2.1 equal.2.2.2)

theorem coordinate_indicators (a b : Address) :
    (if a.diversified.x=b.diversified.x then (1:F) else 0)*
    (if a.diversified.y=b.diversified.y then (1:F) else 0)*
    (if a.transmission.x=b.transmission.x then (1:F) else 0)*
    (if a.transmission.y=b.transmission.y then (1:F) else 0)=
      if a=b then 1 else 0 := by
  by_cases dx : a.diversified.x=b.diversified.x <;>
    by_cases dy : a.diversified.y=b.diversified.y <;>
    by_cases tx : a.transmission.x=b.transmission.x <;>
    by_cases ty : a.transmission.y=b.transmission.y <;>
    simp [address_eq_iff,dx,dy,tx,ty]

structure Inputs (rho : Nat → F) (w : TransferSem.Witness) : Prop where
  regulated : rho 10=if w.regulated then 1 else 0
  context : rho 7607=(w.volume.context:F)
  useReal : rho 7605=if w.volume.useReal then 1 else 0
  same0 : rho 7597=if w.sender.address.diversified.x=w.receiver.address.diversified.x then 1 else 0
  same1 : rho 7599=if w.sender.address.diversified.y=w.receiver.address.diversified.y then 1 else 0
  same2 : rho 7601=if w.sender.address.transmission.x=w.receiver.address.transmission.x then 1 else 0
  same3 : rho 7603=if w.sender.address.transmission.y=w.receiver.address.transmission.y then 1 else 0

theorem value (rho : Nat → F) (w : TransferSem.Witness)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (one : rho copy=1) (inputs : Inputs rho w)
    (context : w.volume.context=1 ∨ w.volume.context=2) :
    rho 108486=if flagged w then 1 else 0 := by
  rw [TierFlagCapture618.polynomial rho arithmetic,one,inputs.context,inputs.regulated,
    inputs.useReal,inputs.same0,inputs.same1,inputs.same2,inputs.same3,
    coordinate_indicators]
  by_cases address : w.sender.address=w.receiver.address <;>
    cases regulated : w.regulated <;>
    cases real : w.volume.useReal <;>
    rcases context with context|context <;>
    norm_num [TransferSem.flagged,TransferSem.eligible,TransferSem.external,address,regulated,real,context]

end ShielddSecurity.TierFlagMeaning619
set_option pp.all true in
#check @ShielddSecurity.TierFlagMeaning619.address_eq_iff
#print axioms ShielddSecurity.TierFlagMeaning619.address_eq_iff
set_option pp.all true in
#check @ShielddSecurity.TierFlagMeaning619.coordinate_indicators
#print axioms ShielddSecurity.TierFlagMeaning619.coordinate_indicators
set_option pp.all true in
#check @ShielddSecurity.TierFlagMeaning619.Inputs
#print axioms ShielddSecurity.TierFlagMeaning619.Inputs
set_option pp.all true in
#check @ShielddSecurity.TierFlagMeaning619.value
#print axioms ShielddSecurity.TierFlagMeaning619.value
