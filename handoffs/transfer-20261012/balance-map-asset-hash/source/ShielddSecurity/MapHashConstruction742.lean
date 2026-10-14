import ShielddSecurity.MapHashRows741
import ShielddSecurity.MapQrConstruction733
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapHashConstruction742
open ConcreteJubjubField01 TransferSem
open MapAssignmentValues720 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  MapQrConstruction733.Earlier MapQrConstruction733.Rows CompilerAssertionBlock51.SatisfiesAt

noncomputable def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  MapQrConstruction733.Earlier original (MapAssetHashMeaning740.input c w) c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  MapQrConstruction733.Rows (assignment original (MapAssetHashMeaning740.input c w) c w legal rkInitial authInitial initial senderInitial receiverInitial)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      MapHashRows741.Rows (assignment original (MapAssetHashMeaning740.input c w) c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,qrRows⟩ :=
    MapQrConstruction733.legal_completed original (MapAssetHashMeaning740.input c w) c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,qrRows⟩,
    MapHashRows741.completed_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.MapHashConstruction742

set_option pp.all true in
#check @ShielddSecurity.MapHashConstruction742.Earlier
#print axioms ShielddSecurity.MapHashConstruction742.Earlier

set_option pp.all true in
#check @ShielddSecurity.MapHashConstruction742.legal_completed
#print axioms ShielddSecurity.MapHashConstruction742.legal_completed
