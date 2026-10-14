import ShielddSecurity.VolumeContextJoin861
import ShielddSecurity.VolumeCandidateConstruction859
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeContextConstruction862
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  VolumeCandidateConstruction859.Earlier VolumeCandidateCapture857.Rows VolumeCandidateAssignment854.assignment
  VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  VolumeCandidateConstruction859.Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  VolumeCandidateConstruction859.Rows (VolumeCandidateAssignment854.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := VolumeContextCapture860.Rows

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (VolumeCandidateAssignment854.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    VolumeCandidateConstruction859.legal_completed original c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,rows⟩,
    VolumeContextJoin861.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.VolumeContextConstruction862

set_option pp.all true in
#check @ShielddSecurity.VolumeContextConstruction862.Earlier
#print axioms ShielddSecurity.VolumeContextConstruction862.Earlier

set_option pp.all true in
#check @ShielddSecurity.VolumeContextConstruction862.Rows
#print axioms ShielddSecurity.VolumeContextConstruction862.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumeContextConstruction862.legal_completed
#print axioms ShielddSecurity.VolumeContextConstruction862.legal_completed
