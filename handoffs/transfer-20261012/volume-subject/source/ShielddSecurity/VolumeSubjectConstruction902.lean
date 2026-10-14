import ShielddSecurity.VolumeSubjectJoin901
import ShielddSecurity.RoutingParameterConstruction882
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeSubjectConstruction902
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  RoutingParameterConstruction882.Earlier RoutingParameterCapture880.Rows VolumeHashAssignment892.assignment
  RoutingPrecisionRows819.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  RoutingParameterConstruction882.Earlier (VolumeHashSeed886.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  RoutingParameterConstruction882.Rows (VolumeHashAssignment892.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := VolumeSubjectCapture900.Rows

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (VolumeHashAssignment892.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    RoutingParameterConstruction882.legal_completed (VolumeHashSeed886.seed original w) c w legal
  refine ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,?_⟩,?_⟩
  · simpa only [VolumeHashAssignment892.assignment] using rows
  · exact VolumeSubjectJoin901.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial
end ShielddSecurity.VolumeSubjectConstruction902

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectConstruction902.Earlier
#print axioms ShielddSecurity.VolumeSubjectConstruction902.Earlier

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectConstruction902.Rows
#print axioms ShielddSecurity.VolumeSubjectConstruction902.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumeSubjectConstruction902.legal_completed
#print axioms ShielddSecurity.VolumeSubjectConstruction902.legal_completed
