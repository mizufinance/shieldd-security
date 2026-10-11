import ShielddSecurity.CompilerArithmeticFixed48
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerArithmeticUniqueness49
open Compiler CompilerCompletion CompilerFreshArithmetic35
variable {F : Type} [Field F]
def PrefixAgreement (copy floor : Nat) (left right : Nat → F) :=
  ∀ column,column<floor ∨ column=copy → left column=right column
theorem recipe_agrees (recipe : Recipe) (copy floor : Nat) (left right : Nat → F)
    (valid : recipe.Valid copy floor) (agrees : PrefixAgreement copy floor left right) :
    PrefixAgreement copy (floor+recipe.width) (recipe.run floor left) (recipe.run floor right) := by
  have values (terms : Linear) (included : ∀ term∈terms,term∈recipe.inputs) : eval left terms=eval right terms := by
    apply eval_agrees
    intro term member
    exact agrees term.1 (valid term (included term member))
  intro column bound
  cases recipe with
  | square input =>
    have inputValue:=values input (by intro term member;exact member)
    by_cases equal : column=floor
    · subst column
      simp [Recipe.run,extendSquare,patchAssignment,inputValue,eval]
    · have old : column<floor ∨ column=copy := by change column<floor+1 ∨ column=copy at bound;omega
      rw [recipe_outside (.square input) floor left column (by change column<floor ∨ floor+1≤column;omega),
        recipe_outside (.square input) floor right column (by change column<floor ∨ floor+1≤column;omega)]
      exact agrees column old
  | pair minus plus =>
    have minusValue:=values minus (by intro term member;exact List.mem_append_left _ member)
    have plusValue:=values plus (by intro term member;exact List.mem_append_right _ member)
    by_cases equal : column=floor
    · subst column
      simp [Recipe.run,patchAssignment,pairValues,minusValue,plusValue]
    · by_cases auxiliary : column=floor+1
      · subst column
        simp [Recipe.run,patchAssignment,pairValues,minusValue]
      · have old : column<floor ∨ column=copy := by change column<floor+2 ∨ column=copy at bound;omega
        rw [recipe_outside (.pair minus plus) floor left column (by change column<floor ∨ floor+2≤column;omega),
          recipe_outside (.pair minus plus) floor right column (by change column<floor ∨ floor+2≤column;omega)]
        exact agrees column old
theorem recipes_agree (recipes : List Recipe) (copy floor : Nat) (left right : Nat → F)
    (checked : check copy floor recipes=true) (agrees : PrefixAgreement copy floor left right) :
    PrefixAgreement copy (floor+span recipes) (run floor left recipes) (run floor right recipes) := by
  induction recipes generalizing floor left right with
  | nil => exact agrees
  | cons recipe tail ih =>
    have parts:=Bool.and_eq_true_iff.mp checked
    have first:=recipe_agrees recipe copy floor left right (check_sound copy floor recipe parts.1) agrees
    have later:=ih (floor+recipe.width) (recipe.run floor left) (recipe.run floor right) parts.2 first
    intro column bound
    apply later column
    change column<floor+(recipe.width+span tail) ∨ column=copy at bound
    omega
theorem forest_agrees (program : CompilerArithmeticForest37.Program) (copy floor : Nat) (left right : Nat → F)
    (checked : CompilerArithmeticForest37.check copy floor program=true) (agrees : PrefixAgreement copy floor left right) :
    PrefixAgreement copy (floor+CompilerArithmeticForest37.span program)
      (CompilerArithmeticForest37.run floor left program) (CompilerArithmeticForest37.run floor right program) := by
  induction program generalizing floor left right with
  | leaf recipes => exact recipes_agree recipes copy floor left right checked agrees
  | append before after ihBefore ihAfter =>
    have parts:=Bool.and_eq_true_iff.mp checked
    have first:=ihBefore floor left right parts.1 agrees
    have later:=ihAfter (floor+CompilerArithmeticForest37.span before)
      (CompilerArithmeticForest37.run floor left before) (CompilerArithmeticForest37.run floor right before) parts.2 first
    intro column bound
    apply later column
    change column<floor+(CompilerArithmeticForest37.span before+CompilerArithmeticForest37.span after) ∨ column=copy at bound
    omega
theorem block_agrees (coefficient : Nat → Int) (copy floor length : Nat)
    (block : CompilerArithmeticBlock44.Block coefficient copy floor length) (left right : Nat → F)
    (agrees : PrefixAgreement copy floor left right) :
    PrefixAgreement copy (floor+length)
      (CompilerArithmeticBlock44.completed coefficient copy floor length block left)
      (CompilerArithmeticBlock44.completed coefficient copy floor length block right) := by
  have found:=forest_agrees (CompilerCachedArithmetic42.decode coefficient block.tree) copy floor left right
    (by rw [CompilerCachedArithmetic42.decode_check coefficient block.tree block.sized];exact block.checked) agrees
  rw [CompilerCachedArithmetic42.decode_span coefficient block.tree block.sized,block.count_exact] at found
  exact found
theorem unique_completed (coefficient : Nat → Int) (copy floor length : Nat)
    (block : CompilerArithmeticBlock44.Block coefficient copy floor length) (base rho : Nat → F)
    (satisfied : CompilerArithmeticBlock44.SatisfiesAt rho block.actual length)
    (seed : PrefixAgreement copy floor base rho) (four : (4:F)≠0) :
    PrefixAgreement copy (floor+length)
      (CompilerArithmeticBlock44.completed coefficient copy floor length block base) rho := by
  have found:=block_agrees coefficient copy floor length block base rho seed
  rw [CompilerArithmeticFixed48.block_fixed coefficient copy floor length block rho satisfied four] at found
  exact found
end ShielddSecurity.CompilerArithmeticUniqueness49

set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticUniqueness49.PrefixAgreement
#print axioms ShielddSecurity.CompilerArithmeticUniqueness49.PrefixAgreement

set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticUniqueness49.recipe_agrees
#print axioms ShielddSecurity.CompilerArithmeticUniqueness49.recipe_agrees

set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticUniqueness49.recipes_agree
#print axioms ShielddSecurity.CompilerArithmeticUniqueness49.recipes_agree

set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticUniqueness49.forest_agrees
#print axioms ShielddSecurity.CompilerArithmeticUniqueness49.forest_agrees

set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticUniqueness49.block_agrees
#print axioms ShielddSecurity.CompilerArithmeticUniqueness49.block_agrees

set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticUniqueness49.unique_completed
#print axioms ShielddSecurity.CompilerArithmeticUniqueness49.unique_completed
