import ShielddSecurity.BalanceBlindingConstruction687
import ShielddSecurity.BalanceBlindingCanonical691
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceCanonicalConstruction692
open ConcreteJubjubField01 TransferSem
open BalanceBlindingBindings680 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model
  BalanceBlindingConstruction687.Earlier BalanceBlindingConstruction687.Rows
noncomputable def Rows (rho : Nat → F) : Prop :=
  CompilerAssertionBlock51.SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+22557+i)) 2
noncomputable def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  BalanceBlindingConstruction687.Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  BalanceBlindingConstruction687.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧ Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,blindingRows⟩ :=
    BalanceBlindingConstruction687.legal_completed original c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,blindingRows⟩,
    BalanceBlindingCanonical691.rows original c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.BalanceCanonicalConstruction692

set_option pp.all true in
#check @ShielddSecurity.BalanceCanonicalConstruction692.Rows
#print axioms ShielddSecurity.BalanceCanonicalConstruction692.Rows

set_option pp.all true in
#check @ShielddSecurity.BalanceCanonicalConstruction692.Earlier
#print axioms ShielddSecurity.BalanceCanonicalConstruction692.Earlier

set_option pp.all true in
#check @ShielddSecurity.BalanceCanonicalConstruction692.legal_completed
#print axioms ShielddSecurity.BalanceCanonicalConstruction692.legal_completed
