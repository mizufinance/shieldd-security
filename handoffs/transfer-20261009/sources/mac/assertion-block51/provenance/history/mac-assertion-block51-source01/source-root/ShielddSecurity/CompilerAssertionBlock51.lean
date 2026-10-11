import ShielddSecurity.Compiler
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerAssertionBlock51
open Compiler
inductive Recipe where
  | linear (left right : Linear)
  | square (left right : Linear)
def expected : Recipe → Row
  | .linear left right => ⟨subtract left right,[]⟩
  | .square left right => ⟨left,right⟩
def sourceLeft : Recipe → Expression
  | .linear left _ => .linear left
  | .square left _ => .square left
def sourceRight : Recipe → Expression
  | .linear _ right | .square _ right => .linear right
def normalized (copy : Nat) (outlined : Bool) (actual : Row) : Row :=
  if outlined then ⟨unoutline copy actual.a,unoutline copy actual.b⟩ else actual
def checkRow (p copy : Nat) (actual : Row) (recipe : Bool × Recipe) : Bool :=
  decide (canonical p (normalized copy recipe.1 actual).a=canonical p (expected recipe.2).a ∧
    canonical p (normalized copy recipe.1 actual).b=canonical p (expected recipe.2).b)
variable {F : Type} [Field F]
def Truth (rho : Nat → F) (recipe : Recipe) :=
  expressionValue rho (sourceLeft recipe)=expressionValue rho (sourceRight recipe)
theorem expected_iff (rho : Nat → F) (recipe : Recipe) :
    Square (eval rho (expected recipe).a) (eval rho (expected recipe).b) ↔ Truth rho recipe := by
  cases recipe with
  | linear left right =>
    change Square (eval rho (subtract left right)) (eval rho []) ↔ eval rho left=eval rho right
    rw [eval_subtract]
    constructor
    · intro satisfied
      exact sub_eq_zero.mp (square_zero _ (by simpa only [eval] using satisfied))
    · intro same
      rw [same,sub_self]
      simp [Square,eval]
  | square left right => rfl
theorem checked_iff {p : Nat} [CharP F p] (copy : Nat) (actual : Row)
    (recipe : Bool × Recipe) (checked : checkRow p copy actual recipe=true)
    (rho : Nat → F) (linked : rho copy=rho 0) :
    Square (eval rho actual.a) (eval rho actual.b) ↔ Truth rho recipe.2 := by
  have h:=of_decide_eq_true checked
  have left:=canonical_equal rho (normalized copy recipe.1 actual).a (expected recipe.2).a h.1
  have right:=canonical_equal rho (normalized copy recipe.1 actual).b (expected recipe.2).b h.2
  have normalizedLeft : eval rho (normalized copy recipe.1 actual).a=eval rho actual.a := by
    cases flag:recipe.1 <;> simp [normalized,flag,eval_unoutline rho copy actual.a linked]
  have normalizedRight : eval rho (normalized copy recipe.1 actual).b=eval rho actual.b := by
    cases flag:recipe.1 <;> simp [normalized,flag,eval_unoutline rho copy actual.b linked]
  rw [←normalizedLeft,←normalizedRight,left,right]
  exact expected_iff rho recipe.2
structure Block (p copy length : Nat) where
  actual : Nat → Option Row
  recipe : Nat → Option (Bool × Recipe)
  exact_checked : ∀ index<length,∃ row hint,actual index=some row ∧
    recipe index=some hint ∧ checkRow p copy row hint=true
def checkList (p copy : Nat) (actual : List Row) (recipes : List (Bool × Recipe)) : Bool :=
  (List.range actual.length).all (fun index =>
    match actual[index]?,recipes[index]? with
    | some row,some hint => checkRow p copy row hint
    | _,_ => false)
noncomputable def leaf (p copy length : Nat) (actual : List Row) (recipes : List (Bool × Recipe))
    (count : actual.length=length) (checked : checkList p copy actual recipes=true) :
    Block p copy length where
  actual := fun index => actual[index]?
  recipe := fun index => recipes[index]?
  exact_checked := by
    intro index bound
    have h:=List.all_eq_true.mp checked index (List.mem_range.mpr (by omega))
    cases foundRow:actual[index]? with
    | none => simp only [checkList,foundRow] at h; contradiction
    | some row =>
      cases foundHint:recipes[index]? with
      | none => simp only [foundRow,foundHint] at h; contradiction
      | some hint => exact ⟨row,hint,foundRow,foundHint,by simpa only [foundRow,foundHint] using h⟩
noncomputable def append (p copy leftLength rightLength : Nat)
    (left : Block p copy leftLength) (right : Block p copy rightLength) :
    Block p copy (leftLength+rightLength) where
  actual := fun index => if index<leftLength then left.actual index else right.actual (index-leftLength)
  recipe := fun index => if index<leftLength then left.recipe index else right.recipe (index-leftLength)
  exact_checked := by
    intro index bound
    by_cases before:index<leftLength
    · simpa only [before,if_true] using left.exact_checked index before
    · simpa only [before,if_false] using right.exact_checked (index-leftLength) (by omega)
theorem every_position (p copy length : Nat) (block : Block p copy length)
    (index : Nat) (bound : index<length) : ∃ row,block.actual index=some row := by
  obtain ⟨row,hint,found,_,_⟩:=block.exact_checked index bound
  exact ⟨row,found⟩
def SatisfiesAt (rho : Nat → F) (actual : Nat → Option Row) (length : Nat) :=
  ∀ index<length,∀ row,actual index=some row → Square (eval rho row.a) (eval rho row.b)
def TruthAt (rho : Nat → F) (recipes : Nat → Option (Bool × Recipe)) (length : Nat) :=
  ∀ index<length,∀ hint,recipes index=some hint → Truth rho hint.2
theorem satisfies_iff {p : Nat} [CharP F p] (copy length : Nat)
    (block : Block p copy length) (rho : Nat → F) (linked : rho copy=rho 0) :
    SatisfiesAt rho block.actual length ↔ TruthAt rho block.recipe length := by
  constructor
  · intro satisfied index bound hint foundHint
    obtain ⟨row,known,foundRow,foundKnown,checked⟩:=block.exact_checked index bound
    have same:known=hint:=Option.some.inj (foundKnown.symm.trans foundHint)
    subst known
    exact (checked_iff copy row hint checked rho linked).mp (satisfied index bound row foundRow)
  · intro truth index bound row foundRow
    obtain ⟨known,hint,foundKnown,foundHint,checked⟩:=block.exact_checked index bound
    have same:known=row:=Option.some.inj (foundKnown.symm.trans foundRow)
    subst known
    exact (checked_iff copy row hint checked rho linked).mpr (truth index bound hint foundHint)
end ShielddSecurity.CompilerAssertionBlock51

set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.Recipe
#print axioms ShielddSecurity.CompilerAssertionBlock51.Recipe
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.expected
#print axioms ShielddSecurity.CompilerAssertionBlock51.expected
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.sourceLeft
#print axioms ShielddSecurity.CompilerAssertionBlock51.sourceLeft
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.sourceRight
#print axioms ShielddSecurity.CompilerAssertionBlock51.sourceRight
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.normalized
#print axioms ShielddSecurity.CompilerAssertionBlock51.normalized
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.checkRow
#print axioms ShielddSecurity.CompilerAssertionBlock51.checkRow
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.Truth
#print axioms ShielddSecurity.CompilerAssertionBlock51.Truth
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.expected_iff
#print axioms ShielddSecurity.CompilerAssertionBlock51.expected_iff
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.checked_iff
#print axioms ShielddSecurity.CompilerAssertionBlock51.checked_iff
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.Block
#print axioms ShielddSecurity.CompilerAssertionBlock51.Block
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.checkList
#print axioms ShielddSecurity.CompilerAssertionBlock51.checkList
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.leaf
#print axioms ShielddSecurity.CompilerAssertionBlock51.leaf
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.append
#print axioms ShielddSecurity.CompilerAssertionBlock51.append
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.every_position
#print axioms ShielddSecurity.CompilerAssertionBlock51.every_position
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.SatisfiesAt
#print axioms ShielddSecurity.CompilerAssertionBlock51.SatisfiesAt
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.TruthAt
#print axioms ShielddSecurity.CompilerAssertionBlock51.TruthAt
set_option pp.all true in
#check @ShielddSecurity.CompilerAssertionBlock51.satisfies_iff
#print axioms ShielddSecurity.CompilerAssertionBlock51.satisfies_iff
