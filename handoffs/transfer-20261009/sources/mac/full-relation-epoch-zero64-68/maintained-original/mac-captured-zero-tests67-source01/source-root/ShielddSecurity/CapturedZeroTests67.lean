import ShielddSecurity.CapturedArithmetic45B0000
import ShielddSecurity.CapturedAssertions50B0000
import ShielddSecurity.CompilerIndexed01
import ShielddSecurity.CompilerZeroTest65
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedZeroTests67
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def arithmetic : List Row := (CapturedArithmetic45B0000.actual.drop 262).take 8
def leftTerms (index : Nat) : Linear := if index<2 then [(35,1)] else [(0,-1),(36,1)]
def rightColumn (index : Nat) : Nat := 116+2*(index/2)-(index%2)
def rightTerms (index : Nat) : Linear := [(rightColumn index,1)]
noncomputable def productCheck : Bool := (List.range 4).all (fun index =>
  CompilerIndexed01.checkUnoutlinedAt p copy arithmetic.toArray (2*index)
    ⟨subtract (leftTerms index) (rightTerms index),[(23001+2*index,1)]⟩ &&
  CompilerIndexed01.checkUnoutlinedAt p copy arithmetic.toArray (2*index+1)
    ⟨leftTerms index++rightTerms index,[(23001+2*index,1)]++scaleLinear 4 [(23000+2*index,1)]⟩)
theorem products_checked : productCheck=true := by decide +kernel
noncomputable def assertions : List Row := (CapturedAssertions50B0000.actual.drop 94).take 6
def recipes : List (Bool × Recipe) :=
  [(false,.square [(115,1)] [(115,1)]),(true,.linear [(23000,1)] [(0,1),(115,-1)]),
   (false,.linear [] [(23002,1)]),(false,.square [(117,1)] [(117,1)]),
   (true,.linear [(23004,1)] [(0,1),(117,-1)]),(false,.linear [] [(23006,1)])]
theorem assertions_checked : checkList p copy assertions recipes=true := by decide +kernel
noncomputable def block : Block p copy 6 := leaf p copy 6 assertions recipes (by decide +kernel) assertions_checked
variable {F : Type} [Field F]
def Primitive (rho : Nat → F) : Prop :=
  CompilerZeroTest65.Primitive (rho 35) (rho 115) (rho 116) ∧
  CompilerZeroTest65.Primitive (rho 36-rho 0) (rho 117) (rho 118)
noncomputable def seeded (base : Nat → F) : Nat → F := fun column =>
  if column=115 then CompilerZeroTest65.indicator (base 35)
  else if column=116 then (base 35)⁻¹
  else if column=117 then CompilerZeroTest65.indicator (base 36-base 0)
  else if column=118 then (base 36-base 0)⁻¹ else base column
theorem seeded_outside (base : Nat → F) (column : Nat)
    (outside : column≠115 ∧ column≠116 ∧ column≠117 ∧ column≠118) :
    seeded base column=base column := by
  simp only [seeded,if_neg outside.1,if_neg outside.2.1,if_neg outside.2.2.1,if_neg outside.2.2.2]
theorem seeded_values (base : Nat → F) :
    seeded base 115=CompilerZeroTest65.indicator (base 35) ∧ seeded base 116=(base 35)⁻¹ ∧
    seeded base 117=CompilerZeroTest65.indicator (base 36-base 0) ∧ seeded base 118=(base 36-base 0)⁻¹ := by
  exact ⟨rfl,rfl,rfl,rfl⟩
theorem seeded_primitive (base : Nat → F) : Primitive (seeded base) := by
  have values:=seeded_values base
  unfold Primitive
  rw [seeded_outside base 35 (by decide),seeded_outside base 36 (by decide),
    seeded_outside base 0 (by decide),values.1,values.2.1,values.2.2.1,values.2.2.2]
  exact ⟨CompilerZeroTest65.complete _,CompilerZeroTest65.complete _⟩
variable [CharP F p]
theorem product_value (rho : Nat → F) (linked : rho copy=rho 0)
    (satisfied : Satisfies rho arithmetic) (index : Nat) (bound : index<4) :
    rho (23000+2*index)=eval rho (leftTerms index)*rho (rightColumn index) := by
  have checks:=Bool.and_eq_true_iff.mp (List.all_eq_true.mp products_checked index (List.mem_range.mpr bound))
  have rows : Satisfies rho (unoutlineRows copy arithmetic) := by
    intro row member
    obtain ⟨original,included,rfl⟩:=List.mem_map.mp member
    simpa only [eval_unoutline rho copy _ linked] using satisfied original included
  have minus:=CompilerIndexed01.checkUnoutlinedAt_sound p copy arithmetic.toArray (2*index)
    ⟨subtract (leftTerms index) (rightTerms index),[(23001+2*index,1)]⟩ checks.1
  have plus:=CompilerIndexed01.checkUnoutlinedAt_sound p copy arithmetic.toArray (2*index+1)
    ⟨leftTerms index++rightTerms index,[(23001+2*index,1)]++scaleLinear 4 [(23000+2*index,1)]⟩ checks.2
  have h:=checked_product_sound rho (unoutlineRows copy arithmetic) (leftTerms index) (rightTerms index)
    [(23000+2*index,1)] [(23001+2*index,1)] four_ne_zero rows
    (by simpa only [List.toList_toArray] using minus) (by simpa only [List.toList_toArray] using plus)
  simpa only [rightTerms,eval,Int.cast_one,one_mul,add_zero] using h
omit [CharP F p] in
theorem assertion_values (rho : Nat → F) (truth : TruthAt rho block.recipe 6) :
    Square (rho 115) (rho 115) ∧ rho 23000=rho 0-rho 115 ∧ rho 23002=0 ∧
    Square (rho 117) (rho 117) ∧ rho 23004=rho 0-rho 117 ∧ rho 23006=0 := by
  have a:=truth 0 (by decide) (false,.square [(115,1)] [(115,1)]) rfl
  have b:=truth 1 (by decide) (true,.linear [(23000,1)] [(0,1),(115,-1)]) rfl
  have c:=truth 2 (by decide) (false,.linear [] [(23002,1)]) rfl
  have d:=truth 3 (by decide) (false,.square [(117,1)] [(117,1)]) rfl
  have e:=truth 4 (by decide) (true,.linear [(23004,1)] [(0,1),(117,-1)]) rfl
  have f:=truth 5 (by decide) (false,.linear [] [(23006,1)]) rfl
  change Square (eval rho [(115,1)]) (eval rho [(115,1)]) at a
  change eval rho [(23000,1)]=eval rho [(0,1),(115,-1)] at b
  change eval rho []=eval rho [(23002,1)] at c
  change Square (eval rho [(117,1)]) (eval rho [(117,1)]) at d
  change eval rho [(23004,1)]=eval rho [(0,1),(117,-1)] at e
  change eval rho []=eval rho [(23006,1)] at f
  simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul] at a b c d e f
  exact ⟨a,by simpa only [sub_eq_add_neg] using b,c.symm,d,by simpa only [sub_eq_add_neg] using e,f.symm⟩
theorem actual_primitive (rho : Nat → F) (zero : rho 0=1) (linked : rho copy=rho 0)
    (arithmeticSatisfied : Satisfies rho arithmetic)
    (assertionsSatisfied : SatisfiesAt rho block.actual 6) : Primitive rho := by
  have values:=assertion_values rho ((satisfies_iff copy 6 block rho linked).mp assertionsSatisfied)
  have a:=product_value rho linked arithmeticSatisfied 0 (by decide)
  have b:=product_value rho linked arithmeticSatisfied 1 (by decide)
  have c:=product_value rho linked arithmeticSatisfied 2 (by decide)
  have d:=product_value rho linked arithmeticSatisfied 3 (by decide)
  simp only [leftTerms,rightColumn,eval,Int.cast_one,Int.cast_neg,one_mul,neg_mul,add_zero] at a b c d
  have c' : rho 23004=(rho 36-rho 0)*rho 118 := by simpa only [sub_eq_add_neg,add_comm] using c
  have d' : rho 23006=(rho 36-rho 0)*rho 117 := by simpa only [sub_eq_add_neg,add_comm] using d
  exact ⟨⟨values.1,a.symm.trans (by simpa only [zero] using values.2.1),b.symm.trans values.2.2.1⟩,
    ⟨values.2.2.2.1,c'.symm.trans (by simpa only [zero] using values.2.2.2.2.1),d'.symm.trans values.2.2.2.2.2⟩⟩
end ShielddSecurity.CapturedZeroTests67

set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.arithmetic
#print axioms ShielddSecurity.CapturedZeroTests67.arithmetic
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.leftTerms
#print axioms ShielddSecurity.CapturedZeroTests67.leftTerms
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.rightColumn
#print axioms ShielddSecurity.CapturedZeroTests67.rightColumn
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.rightTerms
#print axioms ShielddSecurity.CapturedZeroTests67.rightTerms
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.productCheck
#print axioms ShielddSecurity.CapturedZeroTests67.productCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.products_checked
#print axioms ShielddSecurity.CapturedZeroTests67.products_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.assertions
#print axioms ShielddSecurity.CapturedZeroTests67.assertions
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.recipes
#print axioms ShielddSecurity.CapturedZeroTests67.recipes
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.assertions_checked
#print axioms ShielddSecurity.CapturedZeroTests67.assertions_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.block
#print axioms ShielddSecurity.CapturedZeroTests67.block
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.Primitive
#print axioms ShielddSecurity.CapturedZeroTests67.Primitive
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.seeded
#print axioms ShielddSecurity.CapturedZeroTests67.seeded
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.seeded_outside
#print axioms ShielddSecurity.CapturedZeroTests67.seeded_outside
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.seeded_values
#print axioms ShielddSecurity.CapturedZeroTests67.seeded_values
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.seeded_primitive
#print axioms ShielddSecurity.CapturedZeroTests67.seeded_primitive
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.product_value
#print axioms ShielddSecurity.CapturedZeroTests67.product_value
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.assertion_values
#print axioms ShielddSecurity.CapturedZeroTests67.assertion_values
set_option pp.all true in
#check @ShielddSecurity.CapturedZeroTests67.actual_primitive
#print axioms ShielddSecurity.CapturedZeroTests67.actual_primitive
