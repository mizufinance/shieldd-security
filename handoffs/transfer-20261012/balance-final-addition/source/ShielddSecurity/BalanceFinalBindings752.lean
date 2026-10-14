import ShielddSecurity.BalanceFinalAdd747
import ShielddSecurity.BalanceFinalFrame750
import ShielddSecurity.BalanceFinalDomain751
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceFinalBindings752
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open MapAssignmentValues720 (assignment)
attribute [local irreducible] model assignment SatisfiesAt
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem magnitude : VariableWindowColumns449.columnPoint
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) 22230=
      BalanceFinalDomain751.magnitude u w := by
  unfold assignment
  exact BalanceCombined696.magnitude_final_point _ c w legal _ rkInitial authInitial initial senderInitial receiverInitial

theorem flag : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 21711=
    if BalanceSignBindings652.negative w then 1 else 0 := by
  unfold assignment BalanceCombined696.assignment BalanceBlindingBindings680.assignment
  exact BalanceSignBindings652.flag _ _ w legal rkInitial authInitial initial senderInitial receiverInitial

theorem left : Group.Point.mk
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 22230+
     assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 192706)
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 22231)=
      BalanceFinalDomain751.left u w := by
  have arithmetic := MapAssignmentValues720.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have signed := BalanceFinalAdd747.sign_value _ arithmetic
  have point := magnitude original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have x := congrArg Group.Point.x point
  have y := congrArg Group.Point.y point
  change assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 22230=(BalanceFinalDomain751.magnitude u w).x at x
  change assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 22231=(BalanceFinalDomain751.magnitude u w).y at y
  rw [signed,flag original u c w legal rkInitial authInitial initial senderInitial receiverInitial,x,y]
  unfold BalanceFinalDomain751.left
  cases BalanceSignBindings652.negative w <;> simp only [Bool.false_eq_true,if_false,if_true,zero_mul,one_mul,add_zero]
  apply congrArg₂ Group.Point.mk
  · ring
  · rfl

theorem right : VariableWindowColumns449.columnPoint
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) 22734=
      BalanceFinalDomain751.right w := by
  unfold assignment BalanceCombined696.assignment
  exact (BalanceBlindingBindings680.final_point _ c w legal rkInitial authInitial initial senderInitial receiverInitial).trans
    (BalanceBlindingDomain670.multiply_coordinates c w.blinding
      (lt_trans (BalanceBlindingBindings680.scalar_bound c w legal) (by decide)))

theorem hint : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 22736=original 22736 := by
  unfold assignment BalanceCombined696.assignment
  rw [BalanceFinalFrame750.blinding_frame _ c w legal rkInitial authInitial initial senderInitial receiverInitial 22736 (by change 22736∈([22736]:List Nat);decide),
    BalanceMagnitudeTrace640.outside _ _ _ 22736 (Or.inr (by decide)),
    BalanceMapSeed703.outside original u 22736 (by decide)]

end ShielddSecurity.BalanceFinalBindings752

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalBindings752.magnitude
#print axioms ShielddSecurity.BalanceFinalBindings752.magnitude

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalBindings752.flag
#print axioms ShielddSecurity.BalanceFinalBindings752.flag

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalBindings752.left
#print axioms ShielddSecurity.BalanceFinalBindings752.left

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalBindings752.right
#print axioms ShielddSecurity.BalanceFinalBindings752.right

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalBindings752.hint
#print axioms ShielddSecurity.BalanceFinalBindings752.hint
