import ShielddSecurity.MapRootCanonicalConstruction731
import ShielddSecurity.MapQrRows732
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapQrConstruction733
open ConcreteJubjubField01 TransferSem
open MapAssignmentValues720 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  MapRootCanonicalConstruction731.Earlier MapRootCanonicalConstruction731.Rows
  CompilerAssertionBlock51.SatisfiesAt

noncomputable def Earlier (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  MapRootCanonicalConstruction731.Earlier original u c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  MapRootCanonicalConstruction731.Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)

noncomputable def Rows (rho : Nat → F) : Prop :=
  CompilerAssertionBlock51.SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+20997+i)) 1

theorem legal_completed (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original u c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,magnitudeRows⟩ :=
    MapRootCanonicalConstruction731.legal_completed original u c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,magnitudeRows⟩,
    MapQrRows732.completed_rows original u c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.MapQrConstruction733

set_option pp.all true in
#check @ShielddSecurity.MapQrConstruction733.Earlier
#print axioms ShielddSecurity.MapQrConstruction733.Earlier

set_option pp.all true in
#check @ShielddSecurity.MapQrConstruction733.Rows
#print axioms ShielddSecurity.MapQrConstruction733.Rows

set_option pp.all true in
#check @ShielddSecurity.MapQrConstruction733.legal_completed
#print axioms ShielddSecurity.MapQrConstruction733.legal_completed
