import ShielddSecurity.IvkInverseSeed426
import ShielddSecurity.CapturedIvkInverse427
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedIvkInverse428
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem IvkInverseSeed426

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (authInitial : Group.Point F)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CapturedIvkInverse427.Rows (assignment original c w authInitial initial senderInitial receiverInitial) := by
  let rho := assignment original c w authInitial initial senderInitial receiverInitial
  have zero := SharedHighZeroRows333.zero
    (UserWordSeed342.seed (EncodedWordBits375.base
      (AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed (seed original w) c w) w authInitial) w senderInitial receiverInitial) w) c w initial
  change rho 0=1 at zero
  have copied := AuthorizationSharedCopy420C.copied (seed original w) c w authInitial initial senderInitial receiverInitial
  change rho copy=1 at copied
  apply CapturedIvkInverse427.complete rho zero (copied.trans zero.symm)
  intro index bound
  have same : index=0 := by omega
  subst index
  have product := CapturedIvkInverse427.products rho
    (AuthorizationSharedFrame420B.arithmetic (seed original w) c w authInitial initial senderInitial receiverInitial) 0 (by decide)
  have operand := IvkInverseDomain425.operand_meaning (seed original w) c w legal authInitial initial senderInitial receiverInitial
  have inverse := completed_inverse original c w authInitial initial senderInitial receiverInitial
  change eval rho (CapturedIvkInverse427.operandTerms 0)=(w.auth.ivk:F) at operand
  change rho (CapturedIvkInverse427.hintColumn 0)=(w.auth.ivk:F)⁻¹ at inverse
  rw [operand,inverse] at product
  exact product.trans (IvkInverseDomain425.inverse_equation c w legal)

theorem arbitrary_full_nonzero (rho : Nat → F) (zero : rho 0=1)
    (sat : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    eval rho (weighted (List.range' 2000 252) 1) ≠ 0 := by
  have arithmetic := ((CapturedFullRelation58.satisfies_split rho).mp sat).1
  have linked := (CapturedFullRelation58.verifier_links rho sat).2.2
  apply CapturedIvkInverse427.sound rho zero linked arithmetic ?_ 0 (by decide)
  intro index before row found
  apply sat (177954+CapturedIvkInverse427.position index) (by
    unfold CapturedIvkInverse427.position
    omega) row found
end ShielddSecurity.SharedIvkInverse428

set_option pp.all true in
#check @ShielddSecurity.SharedIvkInverse428.all_rows
#print axioms ShielddSecurity.SharedIvkInverse428.all_rows

set_option pp.all true in
#check @ShielddSecurity.SharedIvkInverse428.arbitrary_full_nonzero
#print axioms ShielddSecurity.SharedIvkInverse428.arbitrary_full_nonzero
