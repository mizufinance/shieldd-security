import ShielddSecurity.PublishedInverseConstruction593
import ShielddSecurity.OwnershipRowsConstruction656
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OwnershipConstruction608
open ConcreteJubjubField01 TransferSem
open OwnershipBindings604 (assignment)
attribute [local irreducible] assignment SemanticWordFrame373.assignment ConcreteRegistrySharedEncoding294.model
  PublishedInverseConstruction593.Earlier
noncomputable def Rows (rho : Nat → F) : Prop := OwnershipRowsConstruction656.Rows rho
noncomputable def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  PublishedInverseConstruction593.Earlier (OwnershipTrace603.seed original c w legal) c w legal
    rkInitial authInitial initial senderInitial receiverInitial ∧
  ∀ family,PublishedInverse588.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) family

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
      Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,inverseRows⟩ :=
    PublishedInverseConstruction593.legal_completed (OwnershipTrace603.seed original c w legal) c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,by simpa only [assignment] using inverseRows⟩,
    OwnershipRowsConstruction656.all_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.OwnershipConstruction608

set_option pp.all true in
#check @ShielddSecurity.OwnershipConstruction608.Rows
#print axioms ShielddSecurity.OwnershipConstruction608.Rows

set_option pp.all true in
#check @ShielddSecurity.OwnershipConstruction608.Earlier
#print axioms ShielddSecurity.OwnershipConstruction608.Earlier

set_option pp.all true in
#check @ShielddSecurity.OwnershipConstruction608.legal_completed
#print axioms ShielddSecurity.OwnershipConstruction608.legal_completed
