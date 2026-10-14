import ShielddSecurity.VolumeCandidateValues856
import ShielddSecurity.VolumeContextCapture860
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeContextJoin861
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model SatisfiesAt
  VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

theorem same_address (rho : Nat → F) (w : TransferSem.Witness)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (inputs : TierFlagMeaning619.Inputs rho w) :
    rho 108458=if w.sender.address=w.receiver.address then 1 else 0 := by
  have e0 := TierFlagCapture618.same01_value rho arithmetic
  have e1 := TierFlagCapture618.same012_value rho arithmetic
  have e2 := TierFlagCapture618.same0123_value rho arithmetic
  simp only [eval,Int.cast_one,one_mul,add_zero] at e0 e1 e2
  rw [e2,e1,e0,inputs.same0,inputs.same1,inputs.same2,inputs.same3]
  exact TierFlagMeaning619.coordinate_indicators _ _

theorem generic_rows (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness) (volume : VolumeSem c w)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (one : rho copy=1)
    (inputs : TierFlagMeaning619.Inputs rho w) : VolumeContextCapture860.Rows rho := by
  have captured := VolumeContextCapture860.feeExternal_equation rho arithmetic
  simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at captured
  have captured : rho 121562=(rho 7607-rho copy)*(rho copy-rho 108458) := by
    simpa only [copy,sub_eq_add_neg,add_comm] using captured
  rw [one,inputs.context,same_address rho w arithmetic inputs] at captured
  apply VolumeContextCapture860.rows rho
  rw [captured]
  rcases volume.2.2.2.2.1 with context|context
  · norm_num [context]
  · have equal : w.sender.address=w.receiver.address := by
      have internal := volume.2.2.2.2.2.1 context
      simpa [external] using internal
    norm_num [context,equal]

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VolumeContextCapture860.Rows (VolumeCandidateAssignment854.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  apply generic_rows _ (BalanceBlindingDomain670.crypto c) w legal.2.1.2.2.2.2.2.2.1
  · unfold VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
    exact VolumeTransitionBindings827.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · unfold VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
    exact VolumeTransitionBindings827.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · unfold VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
    exact VolumeTransitionBindings827.inputs _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
end ShielddSecurity.VolumeContextJoin861

set_option pp.all true in
#check @ShielddSecurity.VolumeContextJoin861.same_address
#print axioms ShielddSecurity.VolumeContextJoin861.same_address

set_option pp.all true in
#check @ShielddSecurity.VolumeContextJoin861.generic_rows
#print axioms ShielddSecurity.VolumeContextJoin861.generic_rows

set_option pp.all true in
#check @ShielddSecurity.VolumeContextJoin861.rows
#print axioms ShielddSecurity.VolumeContextJoin861.rows
