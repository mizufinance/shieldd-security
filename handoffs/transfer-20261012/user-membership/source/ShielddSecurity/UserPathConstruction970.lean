import ShielddSecurity.UserPathJoin969
import ShielddSecurity.VolumePathConstruction952
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathConstruction970
open ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt
  VolumePathConstruction952.Earlier VolumePathCapture950.Rows VolumePathAssignment942.assignment

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  VolumePathConstruction952.Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  VolumePathConstruction952.Rows (VolumePathAssignment942.assignment original (BalanceFinalConstruction754.input c w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

abbrev Rows := UserPathCapture968.Rows (F:=F)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (VolumePathAssignment942.assignment original (BalanceFinalConstruction754.input c w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,rows⟩ :=
    VolumePathConstruction952.legal_completed original c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,rows⟩,
    UserPathJoin969.rows original (BalanceFinalConstruction754.input c w) (MapAssetDomain743.withAsset c) w legal
      rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.UserPathConstruction970

set_option pp.all true in
#check @ShielddSecurity.UserPathConstruction970.Earlier
#print axioms ShielddSecurity.UserPathConstruction970.Earlier

set_option pp.all true in
#check @ShielddSecurity.UserPathConstruction970.Rows
#print axioms ShielddSecurity.UserPathConstruction970.Rows

set_option pp.all true in
#check @ShielddSecurity.UserPathConstruction970.legal_completed
#print axioms ShielddSecurity.UserPathConstruction970.legal_completed
