import ShielddSecurity.CompilerArithmeticBlock44
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerArithmeticFixed48
open Compiler CompilerCompletion CompilerFreshArithmetic35
variable {F : Type} [Field F]
theorem recipe_fixed (recipe : Recipe) (floor : Nat) (rho : Nat → F)
    (satisfied : Satisfies rho (recipe.rows floor)) (four : (4:F)≠0) :
    recipe.run floor rho=rho := by
  cases recipe with
  | square input =>
    have value:=satisfied ⟨input,[(floor,1)]⟩ (by simp only [Recipe.rows,List.mem_singleton])
    have square : (eval rho input)^2=rho floor := by
      simpa only [Square,eval,Int.cast_one,one_mul,add_zero,pow_two] using value
    funext column
    by_cases equal : column=floor
    · subst column
      simp [Recipe.run,extendSquare,patchAssignment,square,eval]
    · simp [Recipe.run,extendSquare,patchAssignment,equal]
  | pair minus plus =>
    have first:=satisfied ⟨minus,[(floor+1,1)]⟩ (by simp only [Recipe.rows,List.mem_cons,true_or])
    have second:=satisfied ⟨plus,[(floor,4),(floor+1,1)]⟩ (by simp [Recipe.rows])
    have minusValue : (eval rho minus)^2=rho (floor+1) := by
      simpa only [Square,eval,Int.cast_one,one_mul,add_zero,pow_two] using first
    have plusValue : (eval rho plus)^2=4*rho floor+rho (floor+1) := by
      simpa only [Square,eval,Int.cast_ofNat,Int.cast_one,one_mul,add_zero,pow_two] using second
    have output : ((eval rho plus)^2-(eval rho minus)^2)/4=rho floor := by
      apply (div_eq_iff four).mpr
      rw [plusValue,minusValue]
      ring
    funext column
    by_cases equal : column=floor
    · subst column
      simp [Recipe.run,patchAssignment,pairValues,output]
    · by_cases auxiliary : column=floor+1
      · subst column
        simp [Recipe.run,patchAssignment,pairValues,minusValue]
      · simp [Recipe.run,patchAssignment,pairValues,equal,auxiliary]
theorem recipes_fixed (recipes : List Recipe) (floor : Nat) (rho : Nat → F)
    (satisfied : Satisfies rho (rows floor recipes)) (four : (4:F)≠0) :
    run floor rho recipes=rho := by
  induction recipes generalizing floor with
  | nil => rfl
  | cons recipe tail ih =>
    have first : Satisfies rho (recipe.rows floor) := by
      intro row member
      exact satisfied row (List.mem_append_left _ member)
    have later : Satisfies rho (rows (floor+recipe.width) tail) := by
      intro row member
      exact satisfied row (List.mem_append_right _ member)
    change run (floor+recipe.width) (recipe.run floor rho) tail=rho
    rw [recipe_fixed recipe floor rho first four]
    exact ih (floor+recipe.width) later
theorem forest_fixed (program : CompilerArithmeticForest37.Program) (floor : Nat) (rho : Nat → F)
    (satisfied : CompilerArithmeticForest37.SatisfiesAt rho floor program) (four : (4:F)≠0) :
    CompilerArithmeticForest37.run floor rho program=rho := by
  induction program generalizing floor with
  | leaf recipes =>
    apply recipes_fixed recipes floor rho _ four
    intro row member
    obtain ⟨index,bound,equal⟩:=List.mem_iff_getElem.mp member
    have found : (rows floor recipes)[index]?=some row := by
      rw [List.getElem?_eq_getElem bound,equal]
    exact satisfied index (by change index<span recipes;rw [←CompilerArithmeticForest37.leaf_rows_length recipes floor];exact bound) row found
  | append left right ihLeft ihRight =>
    have first : CompilerArithmeticForest37.SatisfiesAt rho floor left := by
      intro index bound row found
      apply satisfied index (by change index<CompilerArithmeticForest37.span left+CompilerArithmeticForest37.span right;omega) row
      simpa only [CompilerArithmeticForest37.rowAt,if_pos bound] using found
    have later : CompilerArithmeticForest37.SatisfiesAt rho (floor+CompilerArithmeticForest37.span left) right := by
      intro index bound row found
      apply satisfied (CompilerArithmeticForest37.span left+index) (by change _<CompilerArithmeticForest37.span left+CompilerArithmeticForest37.span right;omega) row
      have before : ¬CompilerArithmeticForest37.span left+index<CompilerArithmeticForest37.span left := by omega
      simpa only [CompilerArithmeticForest37.rowAt,if_neg before,Nat.add_sub_cancel_left] using found
    change CompilerArithmeticForest37.run (floor+CompilerArithmeticForest37.span left) (CompilerArithmeticForest37.run floor rho left) right=rho
    rw [ihLeft floor first]
    exact ihRight (floor+CompilerArithmeticForest37.span left) later
theorem block_fixed (coefficient : Nat → Int) (copy floor length : Nat)
    (block : CompilerArithmeticBlock44.Block coefficient copy floor length) (rho : Nat → F)
    (satisfied : CompilerArithmeticBlock44.SatisfiesAt rho block.actual length) (four : (4:F)≠0) :
    CompilerArithmeticBlock44.completed coefficient copy floor length block rho=rho := by
  apply forest_fixed (CompilerCachedArithmetic42.decode coefficient block.tree) floor rho _ four
  intro index bound row found
  apply satisfied index (by rw [CompilerCachedArithmetic42.decode_span coefficient block.tree block.sized,block.count_exact] at bound;exact bound) row
  rw [block.actual_exact,CompilerCachedArithmetic42.rowAt_eq coefficient block.tree block.sized]
  exact found
end ShielddSecurity.CompilerArithmeticFixed48

set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticFixed48.recipe_fixed
#print axioms ShielddSecurity.CompilerArithmeticFixed48.recipe_fixed

set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticFixed48.recipes_fixed
#print axioms ShielddSecurity.CompilerArithmeticFixed48.recipes_fixed

set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticFixed48.forest_fixed
#print axioms ShielddSecurity.CompilerArithmeticFixed48.forest_fixed

set_option pp.all true in
#check @ShielddSecurity.CompilerArithmeticFixed48.block_fixed
#print axioms ShielddSecurity.CompilerArithmeticFixed48.block_fixed
