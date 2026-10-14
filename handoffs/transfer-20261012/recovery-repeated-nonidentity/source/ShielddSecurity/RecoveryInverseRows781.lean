import ShielddSecurity.RecoveryInverseBindings780
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RecoveryInverseRows781
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] SatisfiesAt ConcreteRegistrySharedEncoding294.model
  MapAssignmentValues720.assignment BalanceFinalRows753.assignment DetectionNonidentityRows765.assignment
  OutputAmountRows773.assignment RecoveryInverseSeed778.seed

def assignment (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  OutputAmountRows773.assignment (RecoveryInverseSeed778.seed original w)
    u c w legal rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (slot : Fin 2) :
    RecoveryInverseCapture779.Rows
      (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) slot := by
  let seeded := RecoveryInverseSeed778.seed original w
  have one := RecoveryInverseBindings780.copied seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := RecoveryInverseBindings780.arithmetic seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have inverse := (RecoveryInverseBindings780.hint seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial slot).trans
    (RecoveryInverseSeed778.selected original w slot)
  have operand := RecoveryInverseBindings780.operand seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial slot
  have computed := RecoveryInverseCapture779.equation _ arithmetic slot
  rw [inverse,operand] at computed
  have product := computed.trans (inv_mul_cancel₀ (RecoveryInverseSeed778.nonzero
    (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding c)) w legal slot))
  unfold assignment
  exact RecoveryInverseCapture779.rows _ one slot product
end ShielddSecurity.RecoveryInverseRows781

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseRows781.assignment
#print axioms ShielddSecurity.RecoveryInverseRows781.assignment

set_option pp.all true in
#check @ShielddSecurity.RecoveryInverseRows781.rows
#print axioms ShielddSecurity.RecoveryInverseRows781.rows
