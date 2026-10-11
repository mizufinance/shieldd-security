import ShielddSecurity.CapturedFullRelation58
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRelationFixed59
open CompilerArithmeticTransport41
variable {F : Type}
def InputAgreement (left right : Nat → F) :=
  left 0=right 0 ∧ ∀ input<22735,left (3+input)=right (3+input)
theorem seeded_eq (rho : Nat → F)
    (linked : rho 1=rho 22737 ∧ rho 2=rho 9 ∧ rho copy=rho 0) :
    CompilerVerifierLinks53.seeded rho=rho := by
  funext column
  by_cases isCopy : column=copy
  · subst column
    change rho 0=rho copy
    exact linked.2.2.symm
  · by_cases isPublic : column=1
    · subst column
      change rho 22737=rho 1
      exact linked.1.symm
    · by_cases isCommitted : column=2
      · subst column
        change rho 9=rho 2
        exact linked.2.1.symm
      · exact CompilerVerifierLinks53.seeded_outside rho column ⟨isCopy,isPublic,isCommitted⟩
variable [Field F] [CharP F p]
theorem satisfying_fixed (rho : Nat → F)
    (sat : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    CapturedFullRelation58.candidate rho=rho := by
  have links:=CapturedFullRelation58.verifier_links rho sat
  have arithmetic:=(CapturedFullRelation58.satisfies_split rho).mp sat
  change CapturedFullArithmetic52.completed (CompilerVerifierLinks53.seeded rho)=rho
  rw [seeded_eq rho links]
  exact CapturedFullArithmetic52.fixed_point rho arithmetic.1

theorem initial_agreement (rho sigma : Nat → F) (input : InputAgreement rho sigma)
    (left : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (right : CompilerAssertionBlock51.SatisfiesAt sigma CapturedFullRelation58.rowAt 200770) :
    CompilerArithmeticUniqueness49.PrefixAgreement copy 22738 rho sigma := by
  have l:=CapturedFullRelation58.verifier_links rho left
  have r:=CapturedFullRelation58.verifier_links sigma right
  intro column bound
  by_cases copied : column=copy
  · subst column
    exact l.2.2.trans (input.1.trans r.2.2.symm)
  · have before : column<22738 := by omega
    by_cases zero : column=0
    · subst column;exact input.1
    · by_cases isPublic : column=1
      · subst column
        exact l.1.trans ((input.2 22734 (by decide)).trans r.1.symm)
      · by_cases committed : column=2
        · subst column
          exact l.2.1.trans ((input.2 6 (by decide)).trans r.2.1.symm)
        · have original : column-3<22735 := by omega
          have same : 3+(column-3)=column := by omega
          simpa only [same] using input.2 (column-3) original

theorem satisfying_unique (rho sigma : Nat → F) (input : InputAgreement rho sigma)
    (left : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
    (right : CompilerAssertionBlock51.SatisfiesAt sigma CapturedFullRelation58.rowAt 200770) :
    CompilerArithmeticUniqueness49.PrefixAgreement copy 200692 rho sigma :=
  CapturedFullArithmetic52.satisfying_unique rho sigma
    (initial_agreement rho sigma input left right)
    ((CapturedFullRelation58.satisfies_split rho).mp left).1
    ((CapturedFullRelation58.satisfies_split sigma).mp right).1
end ShielddSecurity.CapturedRelationFixed59

set_option pp.all true in
#check @ShielddSecurity.CapturedRelationFixed59.InputAgreement
#print axioms ShielddSecurity.CapturedRelationFixed59.InputAgreement
set_option pp.all true in
#check @ShielddSecurity.CapturedRelationFixed59.seeded_eq
#print axioms ShielddSecurity.CapturedRelationFixed59.seeded_eq
set_option pp.all true in
#check @ShielddSecurity.CapturedRelationFixed59.satisfying_fixed
#print axioms ShielddSecurity.CapturedRelationFixed59.satisfying_fixed
set_option pp.all true in
#check @ShielddSecurity.CapturedRelationFixed59.initial_agreement
#print axioms ShielddSecurity.CapturedRelationFixed59.initial_agreement
set_option pp.all true in
#check @ShielddSecurity.CapturedRelationFixed59.satisfying_unique
#print axioms ShielddSecurity.CapturedRelationFixed59.satisfying_unique
