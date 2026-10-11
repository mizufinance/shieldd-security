import ShielddSecurity.CapturedArithmetic45B0000
import ShielddSecurity.CapturedAssertions50B0000
import ShielddSecurity.CompilerIndexed01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedEpochNonzero61
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def arithmetic : List Row := (CapturedArithmetic45B0000.actual.drop 256).take 6
def leftColumn (index : Nat) : Nat := if index<2 then 34 else 10
def rightColumn (index : Nat) : Nat := if index=0 then 114 else 113
def leftTerms (index : Nat) : Linear := [(leftColumn index,1)]
def rightTerms (index : Nat) : Linear := [(rightColumn index,1)]
noncomputable def productCheck : Bool := (List.range 3).all (fun index =>
  CompilerIndexed01.checkUnoutlinedAt p copy arithmetic.toArray (2*index)
    ⟨subtract (leftTerms index) (rightTerms index),[(22995+2*index,1)]⟩ &&
  CompilerIndexed01.checkUnoutlinedAt p copy arithmetic.toArray (2*index+1)
    ⟨leftTerms index++rightTerms index,[(22995+2*index,1)]++scaleLinear 4 [(22994+2*index,1)]⟩)
theorem products_checked : productCheck=true := by decide +kernel
noncomputable def assertions : List Row := (CapturedAssertions50B0000.actual.drop 90).take 4
def assertionRecipes : List (Bool × Recipe) :=
  [(false,.square [(113,1)] [(113,1)]),
   (true,.linear [(22994,1)] [(0,1),(113,-1)]),
   (false,.linear [] [(22996,1)]),(false,.linear [] [(22998,1)])]
theorem assertions_checked : checkList p copy assertions assertionRecipes=true := by decide +kernel
noncomputable def assertionBlock : Block p copy 4 :=
  leaf p copy 4 assertions assertionRecipes (by decide +kernel) assertions_checked
variable {F : Type} [Field F]
def Primitive (rho : Nat → F) : Prop :=
  Square (rho 113) (rho 113) ∧ rho 34*rho 114=1-rho 113 ∧
  rho 34*rho 113=0 ∧ rho 10*rho 113=0
noncomputable def seeded (base : Nat → F) : Nat → F := fun column =>
  if column=113 then if base 34=0 then 1 else 0
  else if column=114 then (base 34)⁻¹ else base column
theorem seeded_outside (base : Nat → F) (column : Nat) (different : column≠113 ∧ column≠114) :
    seeded base column=base column := by simp only [seeded,if_neg different.1,if_neg different.2]
theorem seeded_values (base : Nat → F) :
    seeded base 113=(if base 34=0 then 1 else 0) ∧ seeded base 114=(base 34)⁻¹ := by
  simp only [seeded,if_true,show ¬114=113 by decide,if_false]
theorem seeded_primitive (base : Nat → F) (legalGuard : base 34=0 → base 10=0) :
    Primitive (seeded base) := by
  have epoch:=seeded_outside base 34 (by decide)
  have regulated:=seeded_outside base 10 (by decide)
  have hints:=seeded_values base
  unfold Primitive
  rw [epoch,regulated,hints.1,hints.2]
  by_cases zero : base 34=0
  · simp [zero,legalGuard zero,Square]
  · simp [zero,Square]
theorem primitive_zero (rho : Nat → F) (primitive : Primitive rho) :
    rho 113=(if rho 34=0 then 1 else 0) := by
  by_cases zero : rho 34=0
  · rw [if_pos zero]
    have h:=primitive.2.1
    rw [zero,zero_mul] at h
    exact (sub_eq_zero.mp h.symm).symm
  · rw [if_neg zero]
    exact (mul_eq_zero.mp primitive.2.2.1).resolve_left zero
theorem primitive_regulated (rho : Nat → F) (primitive : Primitive rho) (regulated : rho 10≠0) :
    rho 34≠0 := by
  intro zero
  have bit : rho 113=1 := by simpa only [zero,if_true] using primitive_zero rho primitive
  have product:=primitive.2.2.2
  rw [bit,mul_one] at product
  exact regulated product
variable [CharP F p]
theorem product_value (rho : Nat → F) (linked : rho copy=rho 0)
    (satisfied : Satisfies rho arithmetic) (index : Nat) (bound : index<3) :
    rho (22994+2*index)=rho (leftColumn index)*rho (rightColumn index) := by
  have checks:=Bool.and_eq_true_iff.mp (List.all_eq_true.mp products_checked index (List.mem_range.mpr bound))
  have rows : Satisfies rho (unoutlineRows copy arithmetic) := by
    intro row member
    obtain ⟨original,included,rfl⟩:=List.mem_map.mp member
    simpa only [eval_unoutline rho copy _ linked] using satisfied original included
  have minus:=CompilerIndexed01.checkUnoutlinedAt_sound p copy arithmetic.toArray (2*index)
    ⟨subtract (leftTerms index) (rightTerms index),[(22995+2*index,1)]⟩ checks.1
  have plus:=CompilerIndexed01.checkUnoutlinedAt_sound p copy arithmetic.toArray (2*index+1)
    ⟨leftTerms index++rightTerms index,[(22995+2*index,1)]++scaleLinear 4 [(22994+2*index,1)]⟩ checks.2
  have h:=checked_product_sound rho (unoutlineRows copy arithmetic) (leftTerms index) (rightTerms index)
    [(22994+2*index,1)] [(22995+2*index,1)] four_ne_zero rows
    (by simpa only [List.toList_toArray] using minus) (by simpa only [List.toList_toArray] using plus)
  simpa only [leftTerms,rightTerms,eval,Int.cast_one,one_mul,add_zero] using h
omit [CharP F p] in
theorem assertion_values (rho : Nat → F) (truth : TruthAt rho assertionBlock.recipe 4) :
    Square (rho 113) (rho 113) ∧ rho 22994=rho 0-rho 113 ∧ rho 22996=0 ∧ rho 22998=0 := by
  have a:=truth 0 (by decide) (false,.square [(113,1)] [(113,1)]) rfl
  have b:=truth 1 (by decide) (true,.linear [(22994,1)] [(0,1),(113,-1)]) rfl
  have c:=truth 2 (by decide) (false,.linear [] [(22996,1)]) rfl
  have d:=truth 3 (by decide) (false,.linear [] [(22998,1)]) rfl
  change Square (eval rho [(113,1)]) (eval rho [(113,1)]) at a
  change eval rho [(22994,1)]=eval rho [(0,1),(113,-1)] at b
  change eval rho []=eval rho [(22996,1)] at c
  change eval rho []=eval rho [(22998,1)] at d
  simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,neg_one_mul] at a b c d
  exact ⟨a,by simpa only [sub_eq_add_neg] using b,c.symm,d.symm⟩
theorem actual_primitive (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmeticSatisfied : Satisfies rho arithmetic)
    (assertionsSatisfied : CompilerAssertionBlock51.SatisfiesAt rho assertionBlock.actual 4) : Primitive rho := by
  have values:=assertion_values rho ((satisfies_iff copy 4 assertionBlock rho linked).mp assertionsSatisfied)
  have a:=product_value rho linked arithmeticSatisfied 0 (by decide)
  have b:=product_value rho linked arithmeticSatisfied 1 (by decide)
  have c:=product_value rho linked arithmeticSatisfied 2 (by decide)
  change rho 22994=rho 34*rho 114 at a
  change rho 22996=rho 34*rho 113 at b
  change rho 22998=rho 10*rho 113 at c
  exact ⟨values.1,a.symm.trans (by simpa only [zero] using values.2.1),
    b.symm.trans values.2.2.1,c.symm.trans values.2.2.2⟩
theorem actual_regulated (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmeticSatisfied : Satisfies rho arithmetic)
    (assertionsSatisfied : CompilerAssertionBlock51.SatisfiesAt rho assertionBlock.actual 4)
    (regulated : rho 10≠0) : rho 34≠0 :=
  primitive_regulated rho (actual_primitive rho zero linked arithmeticSatisfied assertionsSatisfied) regulated
theorem primitive_assertions (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmeticSatisfied : Satisfies rho arithmetic) (primitive : Primitive rho) :
    CompilerAssertionBlock51.SatisfiesAt rho assertionBlock.actual 4 := by
  apply (satisfies_iff copy 4 assertionBlock rho linked).mpr
  intro index bound hint found
  have a:=product_value rho linked arithmeticSatisfied 0 (by decide)
  have b:=product_value rho linked arithmeticSatisfied 1 (by decide)
  have c:=product_value rho linked arithmeticSatisfied 2 (by decide)
  change rho 22994=rho 34*rho 114 at a
  change rho 22996=rho 34*rho 113 at b
  change rho 22998=rho 10*rho 113 at c
  interval_cases index
  · change some (false,Recipe.square [(113,1)] [(113,1)])=some hint at found
    cases found
    change Square (eval rho [(113,1)]) (eval rho [(113,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero] using primitive.1
  · change some (true,Recipe.linear [(22994,1)] [(0,1),(113,-1)])=some hint at found
    cases found
    change eval rho [(22994,1)]=eval rho [(0,1),(113,-1)]
    simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,neg_one_mul]
    simpa only [zero,sub_eq_add_neg] using a.trans primitive.2.1
  · change some (false,Recipe.linear [] [(22996,1)])=some hint at found
    cases found
    change eval rho []=eval rho [(22996,1)]
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (b.trans primitive.2.2.1).symm
  · change some (false,Recipe.linear [] [(22998,1)])=some hint at found
    cases found
    change eval rho []=eval rho [(22998,1)]
    simpa only [eval,Int.cast_one,one_mul,add_zero] using (c.trans primitive.2.2.2).symm
end ShielddSecurity.CapturedEpochNonzero61

set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.arithmetic
#print axioms ShielddSecurity.CapturedEpochNonzero61.arithmetic
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.leftColumn
#print axioms ShielddSecurity.CapturedEpochNonzero61.leftColumn
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.rightColumn
#print axioms ShielddSecurity.CapturedEpochNonzero61.rightColumn
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.leftTerms
#print axioms ShielddSecurity.CapturedEpochNonzero61.leftTerms
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.rightTerms
#print axioms ShielddSecurity.CapturedEpochNonzero61.rightTerms
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.productCheck
#print axioms ShielddSecurity.CapturedEpochNonzero61.productCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.products_checked
#print axioms ShielddSecurity.CapturedEpochNonzero61.products_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.assertions
#print axioms ShielddSecurity.CapturedEpochNonzero61.assertions
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.assertionRecipes
#print axioms ShielddSecurity.CapturedEpochNonzero61.assertionRecipes
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.assertions_checked
#print axioms ShielddSecurity.CapturedEpochNonzero61.assertions_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.assertionBlock
#print axioms ShielddSecurity.CapturedEpochNonzero61.assertionBlock
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.Primitive
#print axioms ShielddSecurity.CapturedEpochNonzero61.Primitive
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.seeded
#print axioms ShielddSecurity.CapturedEpochNonzero61.seeded
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.seeded_outside
#print axioms ShielddSecurity.CapturedEpochNonzero61.seeded_outside
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.seeded_values
#print axioms ShielddSecurity.CapturedEpochNonzero61.seeded_values
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.seeded_primitive
#print axioms ShielddSecurity.CapturedEpochNonzero61.seeded_primitive
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.primitive_zero
#print axioms ShielddSecurity.CapturedEpochNonzero61.primitive_zero
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.primitive_regulated
#print axioms ShielddSecurity.CapturedEpochNonzero61.primitive_regulated
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.product_value
#print axioms ShielddSecurity.CapturedEpochNonzero61.product_value
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.assertion_values
#print axioms ShielddSecurity.CapturedEpochNonzero61.assertion_values
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.actual_primitive
#print axioms ShielddSecurity.CapturedEpochNonzero61.actual_primitive
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.actual_regulated
#print axioms ShielddSecurity.CapturedEpochNonzero61.actual_regulated
set_option pp.all true in
#check @ShielddSecurity.CapturedEpochNonzero61.primitive_assertions
#print axioms ShielddSecurity.CapturedEpochNonzero61.primitive_assertions
