import ShielddSecurity.RoutingParameterJoin881
import ShielddSecurity.VolumeContextConstruction862
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingParameterConstruction882
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  VolumeContextConstruction862.Earlier VolumeContextCapture860.Rows RoutingParameterAssignment872.assignment
  RoutingPrecisionRows819.assignment CheckingInverseRows789.assignment RecoveryInverseRows781.assignment
  OutputAmountRows773.assignment DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  VolumeContextConstruction862.Earlier (RoutingParameterSeed866.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  VolumeContextConstruction862.Rows (RoutingParameterAssignment872.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := RoutingParameterCapture880.Rows (F:=F)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (RoutingParameterAssignment872.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    VolumeContextConstruction862.legal_completed (RoutingParameterSeed866.seed original w) c w legal
  refine ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,?_⟩,?_⟩
  · simpa only [RoutingParameterAssignment872.assignment] using rows
  · exact RoutingParameterJoin881.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial
end ShielddSecurity.RoutingParameterConstruction882

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterConstruction882.Earlier
#print axioms ShielddSecurity.RoutingParameterConstruction882.Earlier

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterConstruction882.Rows
#print axioms ShielddSecurity.RoutingParameterConstruction882.Rows

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterConstruction882.legal_completed
#print axioms ShielddSecurity.RoutingParameterConstruction882.legal_completed
