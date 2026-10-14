import ShielddSecurity.MapNonidentityRows745
import ShielddSecurity.MapHashConstruction742
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapNonidentityConstruction746
open ConcreteJubjubField01 TransferSem
open MapAssignmentValues720 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  MapHashConstruction742.Earlier MapHashRows741.Rows CompilerAssertionBlock51.SatisfiesAt

noncomputable def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  MapHashConstruction742.Earlier original (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  MapHashRows741.Rows (assignment original (MapAssetHashMeaning740.input (MapAssetDomain743.withAsset c) w)
    (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)

noncomputable def Rows (rho : Nat → F) : Prop :=
  CompilerAssertionBlock51.SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+21265+i)) 1

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (assignment original (MapAssetHashMeaning740.input (MapAssetDomain743.withAsset c) w)
        (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,hashRows⟩ :=
    MapHashConstruction742.legal_completed original (MapAssetDomain743.withAsset c) w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,hashRows⟩,
    MapNonidentityRows745.rows original c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.MapNonidentityConstruction746

set_option pp.all true in
#check @ShielddSecurity.MapNonidentityConstruction746.Earlier
#print axioms ShielddSecurity.MapNonidentityConstruction746.Earlier

set_option pp.all true in
#check @ShielddSecurity.MapNonidentityConstruction746.Rows
#print axioms ShielddSecurity.MapNonidentityConstruction746.Rows

set_option pp.all true in
#check @ShielddSecurity.MapNonidentityConstruction746.legal_completed
#print axioms ShielddSecurity.MapNonidentityConstruction746.legal_completed
