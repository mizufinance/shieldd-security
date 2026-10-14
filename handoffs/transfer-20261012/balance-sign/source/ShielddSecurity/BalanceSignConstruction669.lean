import ShielddSecurity.TierConstruction636
import ShielddSecurity.BalanceSignRow655
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceSignConstruction669
open ConcreteJubjubField01 TransferSem
open BalanceSignBindings652 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment ConcreteRegistrySharedEncoding294.model
  TierConstruction636.Earlier TierConstruction636.Rows

noncomputable def Rows (rho : Nat → F) : Prop :=
  CompilerAssertionBlock51.SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (199867+i)) 1
noncomputable def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  TierConstruction636.Earlier (BalanceSignBindings652.seed original w) c w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  TierConstruction636.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,tierRows⟩ :=
    TierConstruction636.legal_completed (BalanceSignBindings652.seed original w) c w legal
  have retained : TierConstruction636.Rows
      (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
    unfold assignment
    exact tierRows
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,retained⟩,
    BalanceSignRow655.row original c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.BalanceSignConstruction669
set_option pp.all true in
#check @ShielddSecurity.BalanceSignConstruction669.Rows
#print axioms ShielddSecurity.BalanceSignConstruction669.Rows
set_option pp.all true in
#check @ShielddSecurity.BalanceSignConstruction669.Earlier
#print axioms ShielddSecurity.BalanceSignConstruction669.Earlier
set_option pp.all true in
#check @ShielddSecurity.BalanceSignConstruction669.legal_completed
#print axioms ShielddSecurity.BalanceSignConstruction669.legal_completed
