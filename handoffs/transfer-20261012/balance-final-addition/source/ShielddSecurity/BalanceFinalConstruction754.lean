import ShielddSecurity.BalanceFinalRows753
import ShielddSecurity.MapNonidentityConstruction746
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceFinalConstruction754
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  MapNonidentityConstruction746.Earlier MapNonidentityConstruction746.Rows

def input (c : Crypto) (w : TransferSem.Witness) : F := MapAssetHashMeaning740.input (MapAssetDomain743.withAsset c) w

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  MapNonidentityConstruction746.Earlier (BalanceFinalDomain751.seed original (input c w) w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  MapNonidentityConstruction746.Rows (BalanceFinalRows753.assignment original (input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

def Rows (rho : Nat → F) : Prop :=
  CompilerAssertionBlock51.SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+22811+i)) 1

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (BalanceFinalRows753.assignment original (input c w) (MapAssetDomain743.withAsset c)
        w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,nonidentity⟩ :=
    MapNonidentityConstruction746.legal_completed (BalanceFinalDomain751.seed original (input c w) w) c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,nonidentity⟩,
    BalanceFinalRows753.rows original (input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.BalanceFinalConstruction754

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalConstruction754.input
#print axioms ShielddSecurity.BalanceFinalConstruction754.input

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalConstruction754.Earlier
#print axioms ShielddSecurity.BalanceFinalConstruction754.Earlier

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalConstruction754.Rows
#print axioms ShielddSecurity.BalanceFinalConstruction754.Rows

set_option pp.all true in
#check @ShielddSecurity.BalanceFinalConstruction754.legal_completed
#print axioms ShielddSecurity.BalanceFinalConstruction754.legal_completed
