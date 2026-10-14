import ShielddSecurity.VolumePathJoin951
import ShielddSecurity.VolumeOutputConstruction925
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathConstruction952
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  VolumeOutputConstruction925.Earlier VolumeOutputCapture922.Rows VolumeHashAssignment892.assignment
  VolumePathAssignment942.assignment VolumePathSeed936.seed
  VolumeBoundaryAssignment842.assignment RoutingPrecisionRows819.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  VolumeOutputConstruction925.Earlier (VolumePathSeed936.seed original w) c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  VolumeOutputConstruction925.Rows (VolumeHashAssignment892.assignment (VolumePathSeed936.seed original w) (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := VolumePathCapture950.Rows (F:=F)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (VolumePathAssignment942.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    VolumeOutputConstruction925.legal_completed (VolumePathSeed936.seed original w) c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,rows⟩,
    VolumePathJoin951.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.VolumePathConstruction952

set_option pp.all true in
#check @ShielddSecurity.VolumePathConstruction952.Earlier
#print axioms ShielddSecurity.VolumePathConstruction952.Earlier

set_option pp.all true in
#check @ShielddSecurity.VolumePathConstruction952.Rows
#print axioms ShielddSecurity.VolumePathConstruction952.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumePathConstruction952.legal_completed
#print axioms ShielddSecurity.VolumePathConstruction952.legal_completed
