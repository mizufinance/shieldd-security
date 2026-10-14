import ShielddSecurity.RoutingPrecisionRows819
import ShielddSecurity.VolumeControlConstruction806
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingPrecisionConstruction820
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  VolumeControlConstruction806.Earlier VolumeControlCapture804.Rows
  CheckingInverseRows789.assignment RecoveryInverseRows781.assignment OutputAmountRows773.assignment
  DetectionNonidentityRows765.assignment BalanceFinalRows753.assignment MapAssignmentValues720.assignment RoutingPrecisionRows819.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  VolumeControlConstruction806.Earlier (RoutingPrecisionSeed811.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  VolumeControlConstruction806.Rows (RoutingPrecisionRows819.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := RoutingPrecisionRows819.Rows

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (RoutingPrecisionRows819.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    VolumeControlConstruction806.legal_completed (RoutingPrecisionSeed811.seed original w) c w legal
  refine ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,?_,
    RoutingPrecisionRows819.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
  unfold Earlier RoutingPrecisionRows819.assignment
  exact ⟨earlier,rows⟩
end ShielddSecurity.RoutingPrecisionConstruction820

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionConstruction820.Earlier
#print axioms ShielddSecurity.RoutingPrecisionConstruction820.Earlier

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionConstruction820.Rows
#print axioms ShielddSecurity.RoutingPrecisionConstruction820.Rows

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionConstruction820.legal_completed
#print axioms ShielddSecurity.RoutingPrecisionConstruction820.legal_completed
