import ShielddSecurity.SharedAuthorizationInverse421
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationSharedConstruction422
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem AuthorizationSharedFrame420B

/-- Exact retained constructor facts, on the assignment with the five shared inverse hints. -/
def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F)
    (initial : Fin 4 → Group.Point F) : Prop :=
  AuthorizationNonidentityConstruction414.Earlier (AuthorizationSharedSeed416.seed original c w) c w
    authInitial senderInitial receiverInitial initial ∧
  CapturedAuthorizationNonidentity412.Rows (assignment original c w authInitial initial senderInitial receiverInitial)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    ∃ authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w authInitial senderInitial receiverInitial initial ∧
      CapturedAuthorizationShared419.Rows (assignment original c w authInitial initial senderInitial receiverInitial) := by
  obtain ⟨authInitial,senderInitial,receiverInitial,initial,previous⟩ :=
    AuthorizationNonidentityConstruction414.legal_completed (AuthorizationSharedSeed416.seed original c w) c w legal
  exact ⟨authInitial,senderInitial,receiverInitial,initial,previous,
    SharedAuthorizationInverse421.all_rows original c w legal authInitial initial senderInitial receiverInitial⟩
end ShielddSecurity.AuthorizationSharedConstruction422

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedConstruction422.Earlier
#print axioms ShielddSecurity.AuthorizationSharedConstruction422.Earlier

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedConstruction422.legal_completed
#print axioms ShielddSecurity.AuthorizationSharedConstruction422.legal_completed
