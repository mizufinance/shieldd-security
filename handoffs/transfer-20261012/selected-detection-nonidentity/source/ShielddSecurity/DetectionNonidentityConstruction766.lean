import ShielddSecurity.DetectionNonidentityRows765
import ShielddSecurity.BalanceSemanticConstruction758
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.DetectionNonidentityConstruction766
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  BalanceSemanticConstruction758.Earlier TransferSem.balance
  MapAssignmentValues720.assignment BalanceFinalRows753.assignment DetectionNonidentityRows765.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  let chosen := MapAssetDomain743.withAsset c
  let seeded := DetectionNonidentityDomain759.seed original (BalanceBlindingDomain670.withBlinding chosen) w
  BalanceSemanticConstruction758.Earlier seeded c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  let rho := DetectionNonidentityRows765.assignment original (BalanceFinalConstruction754.input c w) chosen
    w legal rkInitial authInitial initial senderInitial receiverInitial
  Group.Point.mk (rho 195230) (rho 195234)=
    SubgroupSeedCompletion203.fieldPoint (TransferSem.balance (MapAssetDomain743.crypto c) w)

def Rows (rho : Nat → F) : Prop :=
  CompilerAssertionBlock51.SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+1468+i)) 1

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (DetectionNonidentityRows765.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  let chosen := MapAssetDomain743.withAsset c
  let seeded := DetectionNonidentityDomain759.seed original (BalanceBlindingDomain670.withBlinding chosen) w
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,meaning⟩ :=
    BalanceSemanticConstruction758.legal_completed seeded c w legal
  refine ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,?_,
    DetectionNonidentityRows765.rows original (BalanceFinalConstruction754.input c w) chosen w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
  unfold Earlier DetectionNonidentityRows765.assignment
  exact ⟨earlier,meaning⟩
end ShielddSecurity.DetectionNonidentityConstruction766

set_option pp.all true in
#check @ShielddSecurity.DetectionNonidentityConstruction766.Earlier
#print axioms ShielddSecurity.DetectionNonidentityConstruction766.Earlier

set_option pp.all true in
#check @ShielddSecurity.DetectionNonidentityConstruction766.Rows
#print axioms ShielddSecurity.DetectionNonidentityConstruction766.Rows

set_option pp.all true in
#check @ShielddSecurity.DetectionNonidentityConstruction766.legal_completed
#print axioms ShielddSecurity.DetectionNonidentityConstruction766.legal_completed
