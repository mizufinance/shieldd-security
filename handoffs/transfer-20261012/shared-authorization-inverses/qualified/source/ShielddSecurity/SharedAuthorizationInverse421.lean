import ShielddSecurity.AuthorizationSharedMeaning420
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedAuthorizationInverse421
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem AuthorizationSharedFrame420B

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (authInitial : Group.Point F)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CapturedAuthorizationShared419.Rows (assignment original c w authInitial initial senderInitial receiverInitial) := by
  let rho := assignment original c w authInitial initial senderInitial receiverInitial
  have zero := SharedHighZeroRows333.zero
    (UserWordSeed342.seed (EncodedWordBits375.base
      (AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed original c w) w authInitial) w senderInitial receiverInitial) w) c w initial
  change rho 0=1 at zero
  have copied := AuthorizationSharedCopy420C.copied original c w authInitial initial senderInitial receiverInitial
  change rho copy=1 at copied
  apply CapturedAuthorizationShared419.complete rho zero (copied.trans zero.symm)
  intro index bound
  have product := CapturedAuthorizationShared419.products rho
    (AuthorizationSharedFrame420B.arithmetic original c w authInitial initial senderInitial receiverInitial) index bound
  have operand := AuthorizationSharedMeaning420.operands original c w authInitial initial senderInitial receiverInitial ⟨index,bound⟩
  have inverse := AuthorizationSharedFrame418.completed_inverse original c w authInitial initial senderInitial receiverInitial ⟨index,bound⟩
  change eval rho (CapturedAuthorizationShared419.operandTerms index)=AuthorizationSharedDomain415.operand c w ⟨index,bound⟩ at operand
  change rho (CapturedAuthorizationShared419.hintColumn index)=(AuthorizationSharedDomain415.operand c w ⟨index,bound⟩)⁻¹ at inverse
  rw [operand,inverse] at product
  exact product.trans (AuthorizationSharedDomain415.inverse_equation c w legal ⟨index,bound⟩)

theorem arbitrary_full_nonzero (rho : Nat → F) (zero : rho 0=1)
    (sat : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (index : Nat) (bound : index<5) : eval rho (CapturedAuthorizationShared419.operandTerms index) ≠ 0 := by
  have arithmetic := ((CapturedFullRelation58.satisfies_split rho).mp sat).1
  have linked := (CapturedFullRelation58.verifier_links rho sat).2.2
  apply CapturedAuthorizationShared419.sound rho zero linked arithmetic ?_ index bound
  intro i before row found
  apply sat (177954+CapturedAuthorizationShared419.position i) (by
    unfold CapturedAuthorizationShared419.position
    omega) row found
end ShielddSecurity.SharedAuthorizationInverse421

set_option pp.all true in
#check @ShielddSecurity.SharedAuthorizationInverse421.all_rows
#print axioms ShielddSecurity.SharedAuthorizationInverse421.all_rows

set_option pp.all true in
#check @ShielddSecurity.SharedAuthorizationInverse421.arbitrary_full_nonzero
#print axioms ShielddSecurity.SharedAuthorizationInverse421.arbitrary_full_nonzero
