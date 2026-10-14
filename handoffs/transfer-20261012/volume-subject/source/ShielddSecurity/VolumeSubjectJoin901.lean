import ShielddSecurity.VolumeSubjectValues899
import ShielddSecurity.VolumeSubjectCapture900
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeSubjectJoin901
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumeHashAssignment892 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model SatisfiesAt Poseidon.hash6

theorem generic_rows (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (volume : VolumeSem c w) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (inputs : TierFlagMeaning619.Inputs rho w) (subject : rho 7740=(w.volume.subject:F))
    (hash : eval rho VolumeSubjectHash898.result=(c.hash .volumeSubject (addressFields w.sender.address++[w.asset]):F)) :
    VolumeSubjectCapture900.Rows rho := by
  apply VolumeSubjectCapture900.rows
  rw [VolumeSubjectCapture900.subject_value rho arithmetic,inputs.useReal,subject,hash]
  cases real : w.volume.useReal
  · simp only [Bool.false_eq_true,if_false,zero_mul]
  · have meaning := (volume.2.2.2.2.2.2.2.2.2.2.2.2.1 real).2.1
    rw [meaning]
    simp

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VolumeSubjectCapture900.Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) :=
  generic_rows _ (BalanceBlindingDomain670.crypto c) w legal.2.1.2.2.2.2.2.2.1
    (VolumeSubjectValues899.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (VolumeSubjectValues899.inputs original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (VolumeHashAssignment892.subject original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (VolumeSubjectValues899.hash_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
end ShielddSecurity.VolumeSubjectJoin901

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectJoin901.generic_rows
#print axioms ShielddSecurity.VolumeSubjectJoin901.generic_rows

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectJoin901.rows
#print axioms ShielddSecurity.VolumeSubjectJoin901.rows
