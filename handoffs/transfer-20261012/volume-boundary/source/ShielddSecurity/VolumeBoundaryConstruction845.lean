import ShielddSecurity.VolumeBoundaryJoin844
import ShielddSecurity.VolumeTransitionConstruction830
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeBoundaryConstruction845
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  VolumeTransitionConstruction830.Earlier VolumeTransitionCapture828.Rows VolumeBoundaryAssignment842.assignment
  RoutingPrecisionRows819.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  VolumeTransitionConstruction830.Earlier (VolumeBoundarySeed836.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  VolumeTransitionConstruction830.Rows (VolumeBoundaryAssignment842.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := VolumeBoundaryCapture843.Rows

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (VolumeBoundaryAssignment842.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    VolumeTransitionConstruction830.legal_completed (VolumeBoundarySeed836.seed original w) c w legal
  refine ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,?_⟩,?_⟩
  · simpa only [VolumeBoundaryAssignment842.assignment] using rows
  · exact VolumeBoundaryJoin844.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial
end ShielddSecurity.VolumeBoundaryConstruction845

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryConstruction845.Earlier
#print axioms ShielddSecurity.VolumeBoundaryConstruction845.Earlier

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryConstruction845.Rows
#print axioms ShielddSecurity.VolumeBoundaryConstruction845.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryConstruction845.legal_completed
#print axioms ShielddSecurity.VolumeBoundaryConstruction845.legal_completed
