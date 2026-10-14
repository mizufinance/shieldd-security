import ShielddSecurity.BalanceSemanticJoin757
import ShielddSecurity.BalanceFinalConstruction754
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceSemanticConstruction758
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model
  MapAssignmentValues720.assignment BalanceFinalRows753.assignment CompilerAssertionBlock51.SatisfiesAt
  BalanceFinalConstruction754.Earlier BalanceFinalConstruction754.Rows

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  BalanceFinalConstruction754.Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  BalanceFinalConstruction754.Rows (BalanceFinalRows753.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      let rho := BalanceFinalRows753.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial
      Group.Point.mk (rho 195230) (rho 195234)=
        SubgroupSeedCompletion203.fieldPoint (TransferSem.balance (MapAssetDomain743.crypto c) w) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    BalanceFinalConstruction754.legal_completed original c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,rows⟩,
    BalanceSemanticJoin757.point original c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.BalanceSemanticConstruction758

set_option pp.all true in
#check @ShielddSecurity.BalanceSemanticConstruction758.Earlier
#print axioms ShielddSecurity.BalanceSemanticConstruction758.Earlier

set_option pp.all true in
#check @ShielddSecurity.BalanceSemanticConstruction758.legal_completed
#print axioms ShielddSecurity.BalanceSemanticConstruction758.legal_completed
