import ShielddSecurity.AuthorizationDhSeed473
import ShielddSecurity.DhInverseRows477
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationDhConstruction474
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationDhSeed473
attribute [local irreducible] CapturedFullRelation58.rowAt

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CapturedDhInverse472.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) :=
  DhInverseRows477.rows (assignment original c w legal authInitial initial senderInitial receiverInitial)
    (AuthorizationDhDomain471.point c w legal).x
    (zero original c w legal authInitial initial senderInitial receiverInitial)
    (copied original c w legal authInitial initial senderInitial receiverInitial)
    (arithmetic original c w legal authInitial initial senderInitial receiverInitial)
    (completed_x original c w legal authInitial initial senderInitial receiverInitial)
    (completed_inverse original c w legal authInitial initial senderInitial receiverInitial)
    (AuthorizationDhDomain471.x_nonzero c w legal)

theorem legal_completed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) :
    ∃ authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal authInitial initial senderInitial receiverInitial ∧
      CapturedDhInverse472.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) := by
  obtain ⟨authInitial,senderInitial,receiverInitial,initial,earlier⟩ := retained original c w legal
  exact ⟨authInitial,senderInitial,receiverInitial,initial,earlier,
    all_rows original c w legal authInitial initial senderInitial receiverInitial⟩

theorem arbitrary_full_nonzero (rho : Nat → F) (zero : rho 0=1)
    (sat : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : rho 3763≠0 := by
  have arithmetic := ((CapturedFullRelation58.satisfies_split rho).mp sat).1
  have linked := (CapturedFullRelation58.verifier_links rho sat).2.2
  have nonzero := CapturedDhInverse472.sound rho zero linked arithmetic
    (by
      intro index before row found
      apply sat (177954+CapturedDhInverse472.position index) (by unfold CapturedDhInverse472.position;omega) row found)
    0 (by decide)
  simpa only [CapturedDhInverse472.operandTerms,eval,Int.cast_one,one_mul,add_zero] using nonzero
end ShielddSecurity.AuthorizationDhConstruction474

set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhConstruction474.all_rows
#print axioms ShielddSecurity.AuthorizationDhConstruction474.all_rows

set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhConstruction474.legal_completed
#print axioms ShielddSecurity.AuthorizationDhConstruction474.legal_completed

set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhConstruction474.arbitrary_full_nonzero
#print axioms ShielddSecurity.AuthorizationDhConstruction474.arbitrary_full_nonzero
