import ShielddSecurity.VolumePathComposition949
import ShielddSecurity.VolumePathCapture950
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathJoin951
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 TransferSem
attribute [local irreducible] SatisfiesAt ConcreteRegistrySharedEncoding294.model PoseidonNatural192.hash Poseidon.hash6

theorem generic_rows {G : Type} [Field G] [CharP G p] (rho : Nat → G) (c : Crypto) (w : TransferSem.Witness)
    (volume : VolumeSem c w) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (one : rho copy=1) (real : rho 7605=(if w.volume.useReal then 1 else 0))
    (newDay : rho 7606=(if w.volume.startsNewDay then 1 else 0)) (anchor : rho 3=(w.anchor:G))
    (hash : eval rho VolumePathHash931C148.result=
      (root c .state w.volume.priorPosition
        (volumeState c w.volume.subject w.volume.dayStart w.volume.prior w.volume.priorBlinding) w.volume.priorSiblings:G)) :
    VolumePathCapture950.Rows rho := by
  apply VolumePathCapture950.rows
  rw [VolumePathCapture950.membership_value rho arithmetic,VolumePathCapture950.continuation_value rho arithmetic,
    one,real,newDay,anchor,hash]
  cases used : w.volume.useReal
  · simp only [Bool.false_eq_true,if_false,zero_mul]
  · cases day : w.volume.startsNewDay
    · have continuation := (volume.2.2.2.2.2.2.2.2.2.2.2.2.1 used).2.2.2.2
      simp only [day,Bool.false_eq_true,if_false] at continuation
      rw [continuation.2]
      simp
    · simp only [if_true,sub_self,mul_zero,zero_mul]

open ConcreteJubjubField01
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VolumePathCapture950.Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  apply generic_rows _ (BalanceBlindingDomain670.crypto c) w legal.2.1.2.2.2.2.2.2.1
  · exact VolumePathValues947.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact VolumePathValues947.copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · unfold assignment VolumeHashAssignment892.assignment RoutingParameterAssignment872.assignment VolumeCandidateAssignment854.assignment VolumeBoundaryAssignment842.assignment
    exact (VolumeTransitionBindings827.inputs _ u c w legal rkInitial authInitial initial senderInitial receiverInitial).useReal
  · unfold assignment
    exact VolumePriorValues909.starts_new_day _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact VolumePathValues947.anchor original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  · exact VolumePathComposition949.result original u c w legal rkInitial authInitial initial senderInitial receiverInitial
end ShielddSecurity.VolumePathJoin951

set_option pp.all true in
#check @ShielddSecurity.VolumePathJoin951.generic_rows
#print axioms ShielddSecurity.VolumePathJoin951.generic_rows

set_option pp.all true in
#check @ShielddSecurity.VolumePathJoin951.rows
#print axioms ShielddSecurity.VolumePathJoin951.rows
