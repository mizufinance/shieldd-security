import ShielddSecurity.BalanceSemantic756
import ShielddSecurity.BalanceFinalRows753
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceSemanticJoin757
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] TransferSem.balance ConcreteRegistrySharedEncoding294.model
  MapAssignmentValues720.assignment BalanceFinalRows753.assignment CompilerAssertionBlock51.SatisfiesAt
theorem public_x (c : Crypto) (w : TransferSem.Witness) :
    (TransferSem.publicFields c w)[7]?.getD 0=(TransferSem.balance c w).x := by rfl

theorem public_y (c : Crypto) (w : TransferSem.Witness) :
    (TransferSem.publicFields c w)[8]?.getD 0=(TransferSem.balance c w).y := by rfl

variable (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem point :
    let rho := BalanceFinalRows753.assignment original
      (MapAssetHashMeaning740.input (MapAssetDomain743.withAsset c) w) (MapAssetDomain743.withAsset c)
      w legal rkInitial authInitial initial senderInitial receiverInitial
    Group.Point.mk (rho 195230) (rho 195234)=
      SubgroupSeedCompletion203.fieldPoint (TransferSem.balance (MapAssetDomain743.crypto c) w) :=
  (BalanceFinalRows753.values original (MapAssetHashMeaning740.input (MapAssetDomain743.withAsset c) w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial).2.trans
      (BalanceSemantic756.balance_coordinates c w legal).symm

theorem public_coordinates :
    let rho := BalanceFinalRows753.assignment original
      (MapAssetHashMeaning740.input (MapAssetDomain743.withAsset c) w) (MapAssetDomain743.withAsset c)
      w legal rkInitial authInitial initial senderInitial receiverInitial
    rho 195230=(((TransferSem.publicFields (MapAssetDomain743.crypto c) w)[7]?.getD 0:Nat):F) ∧
    rho 195234=(((TransferSem.publicFields (MapAssetDomain743.crypto c) w)[8]?.getD 0:Nat):F) := by
  have equality := point original c w legal rkInitial authInitial initial senderInitial receiverInitial
  dsimp only
  rw [public_x,public_y]
  exact ⟨congrArg Group.Point.x equality,congrArg Group.Point.y equality⟩
end ShielddSecurity.BalanceSemanticJoin757

set_option pp.all true in
#check @ShielddSecurity.BalanceSemanticJoin757.point
#print axioms ShielddSecurity.BalanceSemanticJoin757.point

set_option pp.all true in
#check @ShielddSecurity.BalanceSemanticJoin757.public_coordinates
#print axioms ShielddSecurity.BalanceSemanticJoin757.public_coordinates

set_option pp.all true in
#check @ShielddSecurity.BalanceSemanticJoin757.public_x
#print axioms ShielddSecurity.BalanceSemanticJoin757.public_x

set_option pp.all true in
#check @ShielddSecurity.BalanceSemanticJoin757.public_y
#print axioms ShielddSecurity.BalanceSemanticJoin757.public_y
