import ShielddSecurity.VolumePriorJoin911
import ShielddSecurity.VolumeSubjectConstruction902
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePriorConstruction912
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  VolumeSubjectConstruction902.Earlier VolumeSubjectCapture900.Rows VolumeHashAssignment892.assignment
  VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  VolumeSubjectConstruction902.Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  VolumeSubjectConstruction902.Rows (VolumeHashAssignment892.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := VolumePriorCapture910.Rows

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (VolumeHashAssignment892.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    VolumeSubjectConstruction902.legal_completed original c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,rows⟩,
    VolumePriorJoin911.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.VolumePriorConstruction912

set_option pp.all true in
#check @ShielddSecurity.VolumePriorConstruction912.Earlier
#print axioms ShielddSecurity.VolumePriorConstruction912.Earlier

set_option pp.all true in
#check @ShielddSecurity.VolumePriorConstruction912.Rows
#print axioms ShielddSecurity.VolumePriorConstruction912.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumePriorConstruction912.legal_completed
#print axioms ShielddSecurity.VolumePriorConstruction912.legal_completed
