import ShielddSecurity.VolumeTransitionBindings827
import ShielddSecurity.VolumeTransitionCapture828
import ShielddSecurity.VolumeTransitionJoin832
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeTransitionRows829
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open RoutingPrecisionRows819 (assignment)
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model SatisfiesAt assignment
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VolumeTransitionCapture828.Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  apply VolumeTransitionJoin832.rows _ (BalanceBlindingDomain670.crypto c) w legal.2.1.2.2.2.2.2.2.1
  · exact VolumeTransitionBindings827.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact VolumeTransitionBindings827.copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact VolumeTransitionBindings827.inputs original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact VolumeTransitionBindings827.starts_new_day original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact VolumeTransitionBindings827.words original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7741 (by decide +kernel)
  · exact VolumeTransitionBindings827.words original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7742 (by decide +kernel)
  · exact VolumeTransitionBindings827.words original u c w legal rkInitial authInitial initial senderInitial receiverInitial 4789 (by decide +kernel)
end ShielddSecurity.VolumeTransitionRows829

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionRows829.rows
#print axioms ShielddSecurity.VolumeTransitionRows829.rows
