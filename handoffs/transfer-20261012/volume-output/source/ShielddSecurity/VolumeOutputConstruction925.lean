import ShielddSecurity.VolumeOutputJoin924
import ShielddSecurity.VolumePriorConstruction912
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeOutputConstruction925
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  VolumePriorConstruction912.Earlier VolumePriorCapture910.Rows VolumeHashAssignment892.assignment
  VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  VolumePriorConstruction912.Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  VolumePriorConstruction912.Rows (VolumeHashAssignment892.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := VolumeOutputCapture922.Rows (F:=F)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (VolumeHashAssignment892.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    VolumePriorConstruction912.legal_completed original c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,rows⟩,
    VolumeOutputJoin924.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.VolumeOutputConstruction925

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputConstruction925.Earlier
#print axioms ShielddSecurity.VolumeOutputConstruction925.Earlier

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputConstruction925.Rows
#print axioms ShielddSecurity.VolumeOutputConstruction925.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputConstruction925.legal_completed
#print axioms ShielddSecurity.VolumeOutputConstruction925.legal_completed
