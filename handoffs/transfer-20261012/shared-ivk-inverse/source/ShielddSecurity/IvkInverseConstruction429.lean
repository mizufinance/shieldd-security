import ShielddSecurity.SharedIvkInverse428
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.IvkInverseConstruction429
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem IvkInverseSeed426

/-- All prior facts on the same assignment, retaining the five shared inverse rows. -/
def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (initial : Fin 4 → Group.Point F) : Prop :=
  AuthorizationSharedConstruction422.Earlier (seed original w) c w
    authInitial senderInitial receiverInitial initial ∧
  CapturedAuthorizationShared419.Rows (assignment original c w authInitial initial senderInitial receiverInitial)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    ∃ authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w authInitial senderInitial receiverInitial initial ∧
      CapturedIvkInverse427.Rows (assignment original c w authInitial initial senderInitial receiverInitial) := by
  obtain ⟨authInitial,senderInitial,receiverInitial,initial,previous⟩ :=
    AuthorizationSharedConstruction422.legal_completed (seed original w) c w legal
  exact ⟨authInitial,senderInitial,receiverInitial,initial,previous,
    SharedIvkInverse428.all_rows original c w legal authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.IvkInverseConstruction429

set_option pp.all true in
#check @ShielddSecurity.IvkInverseConstruction429.Earlier
#print axioms ShielddSecurity.IvkInverseConstruction429.Earlier

set_option pp.all true in
#check @ShielddSecurity.IvkInverseConstruction429.legal_completed
#print axioms ShielddSecurity.IvkInverseConstruction429.legal_completed
