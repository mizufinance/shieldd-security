import ShielddSecurity.VolumePriorValues909
import ShielddSecurity.VolumePriorCapture910
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePriorJoin911
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumeHashAssignment892 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model SatisfiesAt Poseidon.hash6

theorem generic_rows (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (volume : VolumeSem c w) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (one : rho copy=1) (inputs : TierFlagMeaning619.Inputs rho w)
    (newDay : rho 7606=(if w.volume.startsNewDay then 1 else 0))
    (commitment : rho 8386=(w.volume.priorCommitment:F))
    (hash : eval rho VolumePriorHash908.result=
      (volumeState c w.volume.subject w.volume.dayStart w.volume.prior w.volume.priorBlinding:F)) :
    VolumePriorCapture910.Rows rho := by
  apply VolumePriorCapture910.rows
  rw [VolumePriorCapture910.prior_value rho arithmetic,VolumePriorCapture910.continuation_value rho arithmetic,
    one,inputs.useReal,newDay,commitment,hash]
  cases real : w.volume.useReal
  · simp only [Bool.false_eq_true,if_false,zero_mul]
  · cases day : w.volume.startsNewDay
    · have continuation := (volume.2.2.2.2.2.2.2.2.2.2.2.2.1 real).2.2.2.2
      simp only [day,Bool.false_eq_true,if_false] at continuation
      rw [continuation.1]
      simp
    · simp only [if_true,sub_self,mul_zero,zero_mul]

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VolumePriorCapture910.Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) :=
by
  apply generic_rows _ (BalanceBlindingDomain670.crypto c) w legal.2.1.2.2.2.2.2.2.1
  · unfold assignment
    exact RoutingParameterValues879.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · unfold assignment
    exact RoutingParameterValues879.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · unfold assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
    exact VolumeTransitionBindings827.inputs _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact VolumePriorValues909.starts_new_day original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact VolumeHashAssignment892.priorCommitment original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact VolumePriorValues909.hash_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial

end ShielddSecurity.VolumePriorJoin911

set_option pp.all true in
#check @ShielddSecurity.VolumePriorJoin911.generic_rows
#print axioms ShielddSecurity.VolumePriorJoin911.generic_rows

set_option pp.all true in
#check @ShielddSecurity.VolumePriorJoin911.rows
#print axioms ShielddSecurity.VolumePriorJoin911.rows
