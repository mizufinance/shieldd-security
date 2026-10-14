import ShielddSecurity.VolumeBoundaryBindings841
import ShielddSecurity.VolumeTransitionBindings827
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeBoundaryAssignment842
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model RoutingPrecisionRows819.assignment
  SemanticCopiesRows801.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def assignment (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  RoutingPrecisionRows819.assignment (VolumeBoundarySeed836.seed original w) u c w legal
    rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem frame (column : Nat) (member : column∈VolumeBoundaryLayout833.columns) :
    assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial column=
      VolumeBoundarySeed836.seed original w column := by
  have bounds := VolumeBoundaryLayout833.bounds column member
  have preserved := RoutingPrecisionSeed811.outside (VolumeBoundarySeed836.seed original w) w column (Or.inl (by omega))
  unfold assignment RoutingPrecisionRows819.assignment
  exact (VolumeBoundaryBindings841.current_frame _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
    column member (by rw [preserved];exact VolumeBoundarySeed836.boolean original w column)).trans preserved

theorem day_start : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7739=(w.volume.dayStart:F) :=
  (frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial 7739 (by decide +kernel)).trans
    (VolumeBoundarySeed836.day_start original w)

theorem borrow : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8255=VolumeBoundarySeed836.borrow w :=
  (frame original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8255 (by decide +kernel)).trans
    (VolumeBoundarySeed836.borrow_value original w)
end ShielddSecurity.VolumeBoundaryAssignment842

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryAssignment842.frame
#print axioms ShielddSecurity.VolumeBoundaryAssignment842.frame

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryAssignment842.day_start
#print axioms ShielddSecurity.VolumeBoundaryAssignment842.day_start

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryAssignment842.borrow
#print axioms ShielddSecurity.VolumeBoundaryAssignment842.borrow
