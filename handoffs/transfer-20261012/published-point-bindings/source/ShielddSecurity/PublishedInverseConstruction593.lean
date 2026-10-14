import ShielddSecurity.PublishedInverseSeed592
import ShielddSecurity.PublishedPointNonzero587
import ShielddSecurity.PublishedPointConstruction585
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublishedInverseConstruction593
open ConcreteJubjubField01 TransferSem CompilerAssertionBlock51
open PublishedInverseSeed592 (assignment)
attribute [local irreducible] assignment PublishedPointConstruction585.Earlier

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : ∀ family,PublishedInverse588.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) family := by
  intro family
  have one := PublishedInverseSeed592.zero original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have copied := PublishedInverseSeed592.copied original c w legal rkInitial authInitial initial senderInitial receiverInitial
  apply PublishedInverse588.complete _ one (copied.trans one.symm) family
  rw [PublishedInverse588.products _ (PublishedInverseSeed592.arithmetic original c w legal rkInitial authInitial initial senderInitial receiverInitial) family,
    PublishedInverseSeed592.operand original c w legal rkInitial authInitial initial senderInitial receiverInitial family,PublishedInverseSeed592.hint original c w legal rkInitial authInitial initial senderInitial receiverInitial family]
  exact mul_inv_cancel₀ (PublishedPointNonzero587.x_nonzero c w legal family)

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  PublishedPointConstruction585.Earlier (PublishedInverseSeed592.seed original w) c w legal rkInitial authInitial initial senderInitial receiverInitial ∧
  PublishedPointConstruction585.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    ∃ rkInitial authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal rkInitial authInitial initial senderInitial receiverInitial ∧ ∀ family,PublishedInverse588.Rows (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) family := by
  obtain ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,earlier,pointRows⟩ :=
    PublishedPointConstruction585.legal_completed (PublishedInverseSeed592.seed original w) c w legal
  exact ⟨rkInitial,authInitial,senderInitial,receiverInitial,initial,⟨earlier,by simpa only [assignment] using pointRows⟩,all_rows original c w legal rkInitial authInitial initial senderInitial receiverInitial⟩

end ShielddSecurity.PublishedInverseConstruction593

set_option pp.all true in
#check @ShielddSecurity.PublishedInverseConstruction593.all_rows
#print axioms ShielddSecurity.PublishedInverseConstruction593.all_rows

set_option pp.all true in
#check @ShielddSecurity.PublishedInverseConstruction593.Earlier
#print axioms ShielddSecurity.PublishedInverseConstruction593.Earlier

set_option pp.all true in
#check @ShielddSecurity.PublishedInverseConstruction593.legal_completed
#print axioms ShielddSecurity.PublishedInverseConstruction593.legal_completed
