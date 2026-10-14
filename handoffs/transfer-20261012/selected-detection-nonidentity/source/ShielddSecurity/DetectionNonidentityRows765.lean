import ShielddSecurity.DetectionInverseBindings764
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.DetectionNonidentityRows765
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] SatisfiesAt ConcreteRegistrySharedEncoding294.model
  MapAssignmentValues720.assignment BalanceFinalRows753.assignment DetectionNonidentityDomain759.seed

def assignment (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  BalanceFinalRows753.assignment (DetectionNonidentityDomain759.seed original (BalanceBlindingDomain670.withBlinding c) w)
    u c w legal rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+1468+i)) 1 := by
  let seeded := DetectionNonidentityDomain759.seed original (BalanceBlindingDomain670.withBlinding c) w
  have one := DetectionInverseBindings764.copied seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := DetectionInverseBindings764.arithmetic seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have inverse := (DetectionInverseBindings764.hint seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial).trans
    (DetectionNonidentityDomain759.selected original (BalanceBlindingDomain670.withBlinding c) w)
  have value := DetectionInverseBindings764.selected_x seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have computed := DetectionNonidentityCapture763.equation _ arithmetic
  rw [inverse,value] at computed
  have product := computed.trans (inv_mul_cancel₀ (DetectionNonidentityDomain759.x_nonzero
    (BalanceBlindingDomain670.withBlinding c) w legal))
  unfold assignment
  exact DetectionNonidentityCapture763.rows _ one product
end ShielddSecurity.DetectionNonidentityRows765

set_option pp.all true in
#check @ShielddSecurity.DetectionNonidentityRows765.assignment
#print axioms ShielddSecurity.DetectionNonidentityRows765.assignment

set_option pp.all true in
#check @ShielddSecurity.DetectionNonidentityRows765.rows
#print axioms ShielddSecurity.DetectionNonidentityRows765.rows
