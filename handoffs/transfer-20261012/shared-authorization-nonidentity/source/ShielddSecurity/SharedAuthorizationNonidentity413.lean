import ShielddSecurity.AuthorizationSubgroupConstruction411
import ShielddSecurity.CapturedAuthorizationNonidentity412
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedAuthorizationNonidentity413
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  SemanticWordFrame373.assignment (AuthorizationPointSeed405.seed original w authInitial) c w initial senderInitial receiverInitial

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (authInitial : Group.Point F)
    (initial : Fin 4 → Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CapturedAuthorizationNonidentity412.Rows (assignment original c w authInitial initial senderInitial receiverInitial) := by
  let source := EncodedWordBits375.base (AuthorizationPointSeed405.seed original w authInitial) w senderInitial receiverInitial
  let rho := assignment original c w authInitial initial senderInitial receiverInitial
  have zero := SharedHighZeroRows333.zero (UserWordSeed342.seed source w) c w initial
  have linked := SharedComparisonBlocks327.linked (HighZeroSeed329.seed (UserWordSeed342.seed source w) w) c w initial
  have arithmetic := SharedHighZeroRows333.arithmetic (UserWordSeed342.seed source w) c w initial
  change rho 0=1 at zero
  change rho copy=rho 0 at linked
  change CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954 at arithmetic
  have first := AuthorizationPointFrame407.completed_point original c w authInitial initial senderInitial receiverInitial ⟨0,by decide⟩
  have inverse := AuthorizationPointFrame407.completed_point original c w authInitial initial senderInitial receiverInitial ⟨7,by decide⟩
  change rho 1980=(w.auth.ak.x:F) at first
  change rho 1987=(w.auth.ak.x:F)⁻¹ at inverse
  have product := CapturedAuthorizationNonidentity412.products rho arithmetic 0 (by decide)
  change rho 49780=rho 1980*rho 1987 at product
  rw [first,inverse] at product
  have value : rho 49780=1 := product.trans (AuthorizationPointDomain404.inverse_equation c w legal)
  apply CapturedAuthorizationNonidentity412.complete rho zero linked
  intro index bound
  have same : index=0 := by omega
  subst index
  exact value

theorem arbitrary_full_nonzero (rho : Nat → F) (zero : rho 0=1)
    (sat : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    rho 1980 ≠ 0 := by
  have arithmetic := ((CapturedFullRelation58.satisfies_split rho).mp sat).1
  have linked := (CapturedFullRelation58.verifier_links rho sat).2.2
  apply CapturedAuthorizationNonidentity412.sound rho zero linked arithmetic
  intro index bound row found
  apply sat (177954+CapturedAuthorizationNonidentity412.position index) (by
    have same : index=0 := by omega
    subst index
    decide) row found

end ShielddSecurity.SharedAuthorizationNonidentity413

set_option pp.all true in
#check @ShielddSecurity.SharedAuthorizationNonidentity413.assignment
#print axioms ShielddSecurity.SharedAuthorizationNonidentity413.assignment

set_option pp.all true in
#check @ShielddSecurity.SharedAuthorizationNonidentity413.all_rows
#print axioms ShielddSecurity.SharedAuthorizationNonidentity413.all_rows

set_option pp.all true in
#check @ShielddSecurity.SharedAuthorizationNonidentity413.arbitrary_full_nonzero
#print axioms ShielddSecurity.SharedAuthorizationNonidentity413.arbitrary_full_nonzero
