import ShielddSecurity.VolumeTimestampCapture792
import ShielddSecurity.VolumeTimestampBindings791
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeTimestampRows793
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
  DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VolumeTimestampCapture792.Rows
      (CheckingInverseRows789.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) :=
  VolumeTimestampCapture792.satisfies _
    (VolumeTimestampBindings791.relation original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
end ShielddSecurity.VolumeTimestampRows793

set_option pp.all true in
#check @ShielddSecurity.VolumeTimestampRows793.rows
#print axioms ShielddSecurity.VolumeTimestampRows793.rows
