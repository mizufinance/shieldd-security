import ShielddSecurity.BalanceFinalBindings752
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceFinalRows753
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] SatisfiesAt ConcreteRegistrySharedEncoding294.model
  MapAssignmentValues720.assignment BalanceFinalDomain751.seed

def assignment (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  MapAssignmentValues720.assignment (BalanceFinalDomain751.seed original u w) u c w legal
    rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem values :
    let rho := assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial
    rho 195222=1 ∧ Group.Point.mk (rho 195230) (rho 195234)=
      Group.affineAdd (CapturedFirstSubgroup81.d:F) (BalanceFinalDomain751.left u w) (BalanceFinalDomain751.right w) := by
  let seeded := BalanceFinalDomain751.seed original u w
  have one := MapAssignmentValues720.copied seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := MapAssignmentValues720.arithmetic seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have left := BalanceFinalBindings752.left seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have right := BalanceFinalBindings752.right seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have inverse := (BalanceFinalBindings752.hint seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial).trans
    (BalanceFinalDomain751.selected original u w)
  have computed := BalanceFinalAdd747.values _ one arithmetic
  dsimp only at computed
  rw [left,right,inverse] at computed
  unfold assignment
  constructor
  · exact computed.1.trans (inv_mul_cancel₀ (BalanceFinalDomain751.denominator_nonzero u w))
  · exact (congrArg₂ Group.Point.mk computed.2.1 computed.2.2).trans (BalanceFinalDomain751.coordinates u w)

theorem rows : SatisfiesAt
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (fun i => CapturedFullRelation58.rowAt (177954+22811+i)) 1 := by
  have one := MapAssignmentValues720.copied (BalanceFinalDomain751.seed original u w) u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have computed := values original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  unfold assignment at computed ⊢
  exact BalanceFinalAdd747.rows _ one computed.1
end ShielddSecurity.BalanceFinalRows753

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalRows753.assignment
#print axioms ShielddSecurity.BalanceFinalRows753.assignment

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalRows753.values
#print axioms ShielddSecurity.BalanceFinalRows753.values

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalRows753.rows
#print axioms ShielddSecurity.BalanceFinalRows753.rows
