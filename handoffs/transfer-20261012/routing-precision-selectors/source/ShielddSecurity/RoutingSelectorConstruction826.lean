import ShielddSecurity.RoutingSelectorRows825
import ShielddSecurity.RoutingPrecisionConstruction820
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingSelectorConstruction826
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  RoutingPrecisionConstruction820.Earlier RoutingPrecisionRows819.Rows RoutingPrecisionRows819.assignment CheckingInverseRows789.assignment
  RecoveryInverseRows781.assignment OutputAmountRows773.assignment DetectionNonidentityRows765.assignment
  BalanceFinalRows753.assignment MapAssignmentValues720.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  RoutingPrecisionConstruction820.Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  RoutingPrecisionConstruction820.Rows (RoutingPrecisionRows819.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := RoutingSelectorRows825.Rows

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (RoutingPrecisionRows819.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    RoutingPrecisionConstruction820.legal_completed original c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,rows⟩,
    RoutingSelectorRows825.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.RoutingSelectorConstruction826

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorConstruction826.Earlier
#print axioms ShielddSecurity.RoutingSelectorConstruction826.Earlier

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorConstruction826.Rows
#print axioms ShielddSecurity.RoutingSelectorConstruction826.Rows

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorConstruction826.legal_completed
#print axioms ShielddSecurity.RoutingSelectorConstruction826.legal_completed
