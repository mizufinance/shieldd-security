import ShielddSecurity.VolumeCandidateValues856
import ShielddSecurity.VolumeCandidateCapture857
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeCandidateJoin858
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model SatisfiesAt
  VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

theorem generic_rows (rho : Nat → F) (w : TransferSem.Witness)
    (bound : w.volume.prior+(w.outputs 0).amount<2^128)
    (prior : rho 7741=(w.volume.prior:F)) (outbound : rho 4789=((w.outputs 0).amount:F))
    (candidate : fieldBinary ((List.range' 8127 128).map rho)=((w.volume.prior+(w.outputs 0).amount:Nat):F))
    (limit : fieldBinary ((List.range' 7999 128).map rho)=(w.registry.dailyLimit:F))
    (borrow : rho 8255=VolumeBoundarySeed836.borrow w)
    (difference : rho 8256=(BoundedLimbComparison119.difference 128 (w.volume.prior+(w.outputs 0).amount) w.registry.dailyLimit:F)) :
    VolumeCandidateCapture857.Rows rho := by
  apply VolumeCandidateCapture857.rows rho
  · rw [prior,outbound,candidate,Nat.cast_add]
    ring
  · rw [candidate,limit,borrow,difference]
    have balance := BoundedLimbComparison119.field_balance (F:=F) 128
      (w.volume.prior+(w.outputs 0).amount) w.registry.dailyLimit bound
    unfold VolumeBoundarySeed836.borrow
    linear_combination balance

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VolumeCandidateCapture857.Rows (VolumeCandidateAssignment854.assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  apply generic_rows _ w
  · exact legal.2.1.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.1
  · exact VolumeCandidateValues856.words original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7741 (by decide +kernel)
  · exact VolumeCandidateValues856.words original u c w legal rkInitial authInitial initial senderInitial receiverInitial 4789 (by decide +kernel)
  · exact VolumeCandidateValues856.candidate original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact VolumeCandidateValues856.limit original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact VolumeCandidateValues856.borrow original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact VolumeCandidateValues856.words original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8256 (by decide +kernel)
end ShielddSecurity.VolumeCandidateJoin858

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateJoin858.generic_rows
#print axioms ShielddSecurity.VolumeCandidateJoin858.generic_rows

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateJoin858.rows
#print axioms ShielddSecurity.VolumeCandidateJoin858.rows
