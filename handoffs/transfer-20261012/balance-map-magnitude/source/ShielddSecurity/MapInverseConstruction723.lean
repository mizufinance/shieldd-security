import ShielddSecurity.MapMagnitudeConstruction721
import ShielddSecurity.MapInverseRows722
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapInverseConstruction723
open ConcreteJubjubField01 TransferSem
open MapAssignmentValues720 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  MapMagnitudeConstruction721.Earlier MapMagnitudeConstruction721.Rows
  CompilerAssertionBlock51.SatisfiesAt

noncomputable def Earlier (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  MapMagnitudeConstruction721.Earlier original u c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  MapMagnitudeConstruction721.Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)

noncomputable def Rows (rho : Nat → F) : Prop :=
  CompilerAssertionBlock51.SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+21259+i)) 6

theorem legal_completed (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original u c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,magnitudeRows⟩ :=
    MapMagnitudeConstruction721.legal_completed original u c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,magnitudeRows⟩,
    MapInverseRows722.completed_rows original u c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.MapInverseConstruction723

set_option pp.all true in
#check @ShielddSecurity.MapInverseConstruction723.Earlier
#print axioms ShielddSecurity.MapInverseConstruction723.Earlier

set_option pp.all true in
#check @ShielddSecurity.MapInverseConstruction723.Rows
#print axioms ShielddSecurity.MapInverseConstruction723.Rows

set_option pp.all true in
#check @ShielddSecurity.MapInverseConstruction723.legal_completed
#print axioms ShielddSecurity.MapInverseConstruction723.legal_completed
