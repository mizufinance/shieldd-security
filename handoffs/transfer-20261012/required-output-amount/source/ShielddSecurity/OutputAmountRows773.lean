import ShielddSecurity.OutputAmountBindings772
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OutputAmountRows773
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] SatisfiesAt ConcreteRegistrySharedEncoding294.model
  MapAssignmentValues720.assignment BalanceFinalRows753.assignment DetectionNonidentityRows765.assignment OutputAmountDomain767.seed

def assignment (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  DetectionNonidentityRows765.assignment (OutputAmountDomain767.seed original w)
    u c w legal rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+4783+i)) 1 := by
  let seeded := OutputAmountDomain767.seed original w
  have one := OutputAmountBindings772.copied seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := OutputAmountBindings772.arithmetic seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have inverse := (OutputAmountBindings772.hint seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial).trans
    (OutputAmountDomain767.selected original w)
  have amount := OutputAmountBindings772.amount seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have computed := OutputAmountCapture771.equation _ arithmetic
  rw [inverse,amount] at computed
  have product := computed.trans (inv_mul_cancel₀ (OutputAmountDomain767.amount_nonzero
    (BalanceBlindingDomain670.crypto c) w legal))
  unfold assignment
  exact OutputAmountCapture771.rows _ one product
end ShielddSecurity.OutputAmountRows773

set_option pp.all true in
#check @ShielddSecurity.OutputAmountRows773.assignment
#print axioms ShielddSecurity.OutputAmountRows773.assignment

set_option pp.all true in
#check @ShielddSecurity.OutputAmountRows773.rows
#print axioms ShielddSecurity.OutputAmountRows773.rows
