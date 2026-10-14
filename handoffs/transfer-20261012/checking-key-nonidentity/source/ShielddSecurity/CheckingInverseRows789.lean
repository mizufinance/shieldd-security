import ShielddSecurity.CheckingInverseBindings788
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CheckingInverseRows789
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] SatisfiesAt ConcreteRegistrySharedEncoding294.model
  MapAssignmentValues720.assignment BalanceFinalRows753.assignment DetectionNonidentityRows765.assignment
  RecoveryInverseRows781.assignment OutputAmountRows773.assignment CheckingInverseSeed783.seed

def assignment (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  RecoveryInverseRows781.assignment (CheckingInverseSeed783.seed original (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding c)) w)
    u c w legal rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (slot : Fin 2) :
    CheckingInverseCapture787.Rows
      (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) slot := by
  let seeded := CheckingInverseSeed783.seed original (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding c)) w
  have one := CheckingInverseBindings788.copied seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := CheckingInverseBindings788.arithmetic seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have inverse := (CheckingInverseBindings788.hint seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial slot).trans
    (CheckingInverseSeed783.selected original (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding c)) w slot)
  have operand := CheckingInverseBindings788.operand seeded u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have computed := CheckingInverseCapture787.equation _ arithmetic slot
  rw [inverse,operand] at computed
  have product := computed.trans (inv_mul_cancel₀ (CheckingInverseSeed783.nonzero
    (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding c)) w legal))
  unfold assignment
  exact CheckingInverseCapture787.rows _ one slot product
end ShielddSecurity.CheckingInverseRows789

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseRows789.assignment
#print axioms ShielddSecurity.CheckingInverseRows789.assignment

set_option pp.all true in
#check @ShielddSecurity.CheckingInverseRows789.rows
#print axioms ShielddSecurity.CheckingInverseRows789.rows
