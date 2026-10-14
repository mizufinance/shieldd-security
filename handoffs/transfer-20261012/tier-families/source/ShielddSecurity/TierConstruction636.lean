import ShielddSecurity.OwnershipConstruction608
import ShielddSecurity.TierRowsConstruction657
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierConstruction636
open ConcreteJubjubField01 TransferSem
open TierFlagBindings630 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment ConcreteRegistrySharedEncoding294.model
  OwnershipConstruction608.Earlier OwnershipConstruction608.Rows
noncomputable def Rows (rho : Nat → F) : Prop := TierRowsConstruction657.Rows rho
set_option pp.all true in
#check @ShielddSecurity.TierConstruction636.Rows
#print axioms ShielddSecurity.TierConstruction636.Rows

noncomputable def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  OwnershipConstruction608.Earlier
    (TierTrace616.seed (TierFlagSeed623.seed original w) c w legal)
    (DetectionGroupDomain611.baseCrypto c) w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  OwnershipConstruction608.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)

set_option pp.all true in
#check @ShielddSecurity.TierConstruction636.Earlier
#print axioms ShielddSecurity.TierConstruction636.Earlier

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,ownershipRows⟩ :=
    OwnershipConstruction608.legal_completed
      (TierTrace616.seed (TierFlagSeed623.seed original w) c w legal)
      (DetectionGroupDomain611.baseCrypto c) w legal
  have retained : OwnershipConstruction608.Rows
      (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
    unfold assignment TierBindings617.assignment
    exact ownershipRows
  have previous : Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial :=
    ⟨earlier,retained⟩
  have current : Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) :=
    TierRowsConstruction657.all_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,previous,current⟩

end ShielddSecurity.TierConstruction636



set_option pp.all true in
#check @ShielddSecurity.TierConstruction636.legal_completed
#print axioms ShielddSecurity.TierConstruction636.legal_completed
