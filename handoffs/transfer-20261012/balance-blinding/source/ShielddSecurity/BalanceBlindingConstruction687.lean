import ShielddSecurity.CapturedBlindingSubgroup671
import ShielddSecurity.BalanceSignConstruction669
import ShielddSecurity.BalanceBlindingRowsConstruction686
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingConstruction687
open ConcreteJubjubField01 TransferSem
open BalanceBlindingBindings680 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment ConcreteRegistrySharedEncoding294.model
  BalanceSignConstruction669.Earlier BalanceSignConstruction669.Rows

noncomputable def Rows (rho : Nat → F) : Prop :=
  BalanceBlindingRowsConstruction686.Rows rho
noncomputable def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  BalanceSignConstruction669.Earlier (BalanceBlindingTrace675.seed original w.blinding) (BalanceBlindingDomain670.withBlinding c) w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  BalanceSignConstruction669.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,tierRows⟩ :=
    BalanceSignConstruction669.legal_completed (BalanceBlindingTrace675.seed original w.blinding) (BalanceBlindingDomain670.withBlinding c) w legal
  have retained : BalanceSignConstruction669.Rows
      (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
    unfold assignment
    exact tierRows
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,retained⟩,
    BalanceBlindingRowsConstruction686.all_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.BalanceBlindingConstruction687
set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingConstruction687.Rows
#print axioms ShielddSecurity.BalanceBlindingConstruction687.Rows
set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingConstruction687.Earlier
#print axioms ShielddSecurity.BalanceBlindingConstruction687.Earlier
set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingConstruction687.legal_completed
#print axioms ShielddSecurity.BalanceBlindingConstruction687.legal_completed
