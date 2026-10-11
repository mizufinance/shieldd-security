import ShielddSecurity.CompilerArithmeticForest37
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerIndexedRecipe38
open Compiler
abbrev Terms := List (Nat×Nat)
def linear (coefficient : Nat → Int) (terms : Terms) : Linear := terms.map (fun term => (term.1,coefficient term.2))
def termsCheck (copy floor : Nat) (terms : Terms) : Bool := terms.all (fun term => decide (term.1<floor ∨ term.1=copy))
theorem linear_check (coefficient : Nat → Int) (copy floor : Nat) (terms : Terms) :
    (linear coefficient terms).all (fun term => decide (term.1<floor ∨ term.1=copy))=termsCheck copy floor terms := by
  simp only [linear,List.all_map,termsCheck,Function.comp_def]
inductive Recipe where
  | square (input : Terms)
  | pair (minus plus : Terms)
def decode (coefficient : Nat → Int) : Recipe → CompilerFreshArithmetic35.Recipe
  | .square input => .square (linear coefficient input)
  | .pair minus plus => .pair (linear coefficient minus) (linear coefficient plus)
def width : Recipe → Nat
  | .square _ => 1
  | .pair _ _ => 2
def recipeCheck (copy floor : Nat) : Recipe → Bool
  | .square input => termsCheck copy floor input
  | .pair minus plus => termsCheck copy floor minus && termsCheck copy floor plus
theorem decode_width (coefficient : Nat → Int) (recipe : Recipe) : (decode coefficient recipe).width=width recipe := by
  cases recipe <;> rfl
theorem decode_check (coefficient : Nat → Int) (copy floor : Nat) (recipe : Recipe) :
    (decode coefficient recipe).check copy floor=recipeCheck copy floor recipe := by
  cases recipe with
  | square input => exact linear_check coefficient copy floor input
  | pair minus plus =>
    change ((linear coefficient minus)++linear coefficient plus).all _=_
    rw [List.all_append,linear_check,linear_check]
    rfl
def decodeList (coefficient : Nat → Int) (recipes : List Recipe) : List CompilerFreshArithmetic35.Recipe := recipes.map (decode coefficient)
def span : List Recipe → Nat
  | [] => 0
  | recipe::tail => width recipe+span tail
def check (copy floor : Nat) : List Recipe → Bool
  | [] => true
  | recipe::tail => recipeCheck copy floor recipe && check copy (floor+width recipe) tail
theorem decode_span (coefficient : Nat → Int) (recipes : List Recipe) : CompilerFreshArithmetic35.span (decodeList coefficient recipes)=span recipes := by
  induction recipes with
  | nil => rfl
  | cons recipe tail ih =>
    simp only [decodeList,List.map_cons,CompilerFreshArithmetic35.span,decode_width]
    exact congrArg (fun n => width recipe+n) ih
theorem decode_list_check (coefficient : Nat → Int) (copy floor : Nat) (recipes : List Recipe) :
    CompilerFreshArithmetic35.check copy floor (decodeList coefficient recipes)=check copy floor recipes := by
  induction recipes generalizing floor with
  | nil => rfl
  | cons recipe tail ih =>
    simp only [decodeList,List.map_cons,CompilerFreshArithmetic35.check,decode_check,decode_width,check]
    exact congrArg (fun b => recipeCheck copy floor recipe && b) (ih (floor+width recipe))
variable {F : Type} [Field F]
theorem complete (coefficient : Nat → Int) (recipes : List Recipe) (copy floor : Nat) (base : Nat → F)
    (checked : check copy floor recipes=true) (below : floor+span recipes≤copy) (four : (4:F)≠0) :
    Satisfies (CompilerFreshArithmetic35.run floor base (decodeList coefficient recipes))
      (CompilerFreshArithmetic35.rows floor (decodeList coefficient recipes)) := by
  apply CompilerFreshArithmetic35.complete
  · rw [decode_list_check];exact checked
  · rw [decode_span];exact below
  · exact four
end ShielddSecurity.CompilerIndexedRecipe38

set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.Terms
#print axioms ShielddSecurity.CompilerIndexedRecipe38.Terms
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.linear
#print axioms ShielddSecurity.CompilerIndexedRecipe38.linear
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.termsCheck
#print axioms ShielddSecurity.CompilerIndexedRecipe38.termsCheck
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.linear_check
#print axioms ShielddSecurity.CompilerIndexedRecipe38.linear_check
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.Recipe
#print axioms ShielddSecurity.CompilerIndexedRecipe38.Recipe
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.decode
#print axioms ShielddSecurity.CompilerIndexedRecipe38.decode
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.width
#print axioms ShielddSecurity.CompilerIndexedRecipe38.width
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.recipeCheck
#print axioms ShielddSecurity.CompilerIndexedRecipe38.recipeCheck
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.decode_width
#print axioms ShielddSecurity.CompilerIndexedRecipe38.decode_width
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.decode_check
#print axioms ShielddSecurity.CompilerIndexedRecipe38.decode_check
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.decodeList
#print axioms ShielddSecurity.CompilerIndexedRecipe38.decodeList
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.span
#print axioms ShielddSecurity.CompilerIndexedRecipe38.span
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.check
#print axioms ShielddSecurity.CompilerIndexedRecipe38.check
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.decode_span
#print axioms ShielddSecurity.CompilerIndexedRecipe38.decode_span
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.decode_list_check
#print axioms ShielddSecurity.CompilerIndexedRecipe38.decode_list_check
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexedRecipe38.complete
#print axioms ShielddSecurity.CompilerIndexedRecipe38.complete
