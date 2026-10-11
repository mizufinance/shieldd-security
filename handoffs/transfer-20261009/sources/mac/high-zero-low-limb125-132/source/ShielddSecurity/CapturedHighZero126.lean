import ShielddSecurity.CapturedHighLimbShared124
import ShielddSecurity.FieldZeroSeed125
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedHighZero126Data
import ShielddSecurity.CapturedArithmetic45B0048
import ShielddSecurity.CapturedAssertions50B0004
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedHighZero126
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def delta : Linear := weighted CapturedRegistryHighLimb120.rightColumns (-1)++weighted CapturedRegistryHighLimb120.leftColumns 1
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.delta
#print axioms ShielddSecurity.CapturedHighZero126.delta
noncomputable def arithmeticRows : List Row := CapturedHighZero126Data.arithmeticRows
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.arithmeticRows
#print axioms ShielddSecurity.CapturedHighZero126.arithmeticRows
noncomputable def actualRows : List Row := CapturedHighZero126Data.actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.actualRows
#print axioms ShielddSecurity.CapturedHighZero126.actualRows
noncomputable def arithmeticCheck : Bool := CapturedHighZero126Data.arithmeticCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.arithmeticCheck
#print axioms ShielddSecurity.CapturedHighZero126.arithmeticCheck
theorem arithmetic_checked : arithmeticCheck=true := CapturedHighZero126Data.arithmetic_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.arithmetic_checked
#print axioms ShielddSecurity.CapturedHighZero126.arithmetic_checked
noncomputable def assertionCheck : Bool := CapturedHighZero126Data.assertionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.assertionCheck
#print axioms ShielddSecurity.CapturedHighZero126.assertionCheck
theorem assertion_checked : assertionCheck=true := CapturedHighZero126Data.assertion_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.assertion_checked
#print axioms ShielddSecurity.CapturedHighZero126.assertion_checked
noncomputable def inverseCheck : Bool := Compiler.checkRow p arithmeticRows ⟨subtract delta [(1111,1)],[(33771,1)]⟩ &&
  Compiler.checkRow p arithmeticRows ⟨delta++[(1111,1)],[(33771,1)]++scaleLinear 4 [(33770,1)]⟩
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.inverseCheck
#print axioms ShielddSecurity.CapturedHighZero126.inverseCheck
theorem inverse_checked : inverseCheck=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.inverse_checked
#print axioms ShielddSecurity.CapturedHighZero126.inverse_checked
noncomputable def zeroCheck : Bool := Compiler.checkRow p arithmeticRows ⟨subtract delta [(1110,1)],[(33773,1)]⟩ &&
  Compiler.checkRow p arithmeticRows ⟨delta++[(1110,1)],[(33773,1)]++scaleLinear 4 [(33772,1)]⟩
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.zeroCheck
#print axioms ShielddSecurity.CapturedHighZero126.zeroCheck
theorem zero_checked : zeroCheck=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.zero_checked
#print axioms ShielddSecurity.CapturedHighZero126.zero_checked
def expected (index : Nat) : Recipe :=
  if index=0 then .square [(1110,1)] [(1110,1)]
  else if index=1 then .linear [(33770,1),(1110,1)] [(0,1)]
  else .linear [] [(33772,1)]
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.expected
#print axioms ShielddSecurity.CapturedHighZero126.expected
noncomputable def productionCheck : Bool := (List.range 3).all (fun index =>
  match actualRows[index]? with
  | some row => CompilerAssertionBlock51.checkRow p copy row (true,expected index)
  | none => false)
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.productionCheck
#print axioms ShielddSecurity.CapturedHighZero126.productionCheck
theorem production_checked : productionCheck=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.production_checked
#print axioms ShielddSecurity.CapturedHighZero126.production_checked
noncomputable def block : Block p copy 3 where
  actual := fun index => actualRows[index]?
  recipe := fun index => some (true,expected index)
  exact_checked := by
    intro index bound
    have h:=List.all_eq_true.mp production_checked index (List.mem_range.mpr bound)
    change (match actualRows[index]? with | some row => CompilerAssertionBlock51.checkRow p copy row (true,expected index) | none => false)=true at h
    cases found:actualRows[index]? with
    | none => simp only [found] at h;contradiction
    | some row => exact ⟨row,(true,expected index),rfl,rfl,by simpa only [found] using h⟩
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.block
#print axioms ShielddSecurity.CapturedHighZero126.block
theorem hint_exact (index : Nat) (hint : Bool × Recipe) (found : block.recipe index=some hint) :
    hint.2=expected index := by
  change some (true,expected index)=some hint at found
  exact congrArg Prod.snd (Option.some.inj found).symm
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.hint_exact
#print axioms ShielddSecurity.CapturedHighZero126.hint_exact
theorem arithmetic_position (index : Nat) (bound : index<4) :
    CapturedFullArithmetic52.rowAt (11032+index)=arithmeticRows[index]? :=
  CapturedHighZero126Data.arithmetic_position index bound
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.arithmetic_position
#print axioms ShielddSecurity.CapturedHighZero126.arithmetic_position
theorem assertion_position (index : Nat) (bound : index<3) :
    CapturedFullRelation58.rowAt (179023+index)=actualRows[index]? :=
  CapturedHighZero126Data.assertion_position index bound
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.assertion_position
#print axioms ShielddSecurity.CapturedHighZero126.assertion_position
variable {F : Type} [Field F] [CharP F p]
theorem products (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 33770=eval rho delta*rho 1111 ∧ rho 33772=eval rho delta*rho 1110 := by
  have sat : Satisfies rho arithmeticRows := by
    intro row member
    obtain ⟨index,found⟩:=List.mem_iff_getElem?.mp member
    obtain ⟨before,_⟩:=List.getElem?_eq_some_iff.mp found
    have bound : index<4 := by
      rw [CompilerRowSlice63.count CapturedArithmetic45B0048.block.actual 440 4 arithmeticRows arithmetic_checked] at before
      exact before
    exact arithmetic (11032+index) (by omega) row ((arithmetic_position index bound).trans found)
  have hi:=checked_product_sound rho arithmeticRows delta [(1111,1)] [(33770,1)] [(33771,1)]
    four_ne_zero sat (Bool.and_eq_true_iff.mp inverse_checked).1 (Bool.and_eq_true_iff.mp inverse_checked).2
  have hz:=checked_product_sound rho arithmeticRows delta [(1110,1)] [(33772,1)] [(33773,1)]
    four_ne_zero sat (Bool.and_eq_true_iff.mp zero_checked).1 (Bool.and_eq_true_iff.mp zero_checked).2
  constructor
  · simpa only [eval,Int.cast_one,one_mul,add_zero] using hi
  · simpa only [eval,Int.cast_one,one_mul,add_zero] using hz
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.products
#print axioms ShielddSecurity.CapturedHighZero126.products
theorem truth (rho : Nat → F) (d : F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (meaning : eval rho delta=d) (flag : rho 1110=FieldZeroSeed125.flag d)
    (inverse : rho 1111=d⁻¹) (one : rho 0=1) : TruthAt rho block.recipe 3 := by
  have pr:=products rho arithmetic
  intro index bound hint found
  rw [hint_exact index hint found]
  have cases : index=0 ∨ index=1 ∨ index=2 := by omega
  rcases cases with rfl | rfl | rfl
  · change Square (eval rho [(1110,1)]) (eval rho [(1110,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero,flag] using FieldZeroSeed125.boolean d
  · change eval rho [(33770,1),(1110,1)]=eval rho [(0,1)]
    simp only [eval,Int.cast_one,one_mul,add_zero]
    rw [pr.1,meaning,inverse,flag,one,FieldZeroSeed125.inverse]
    ring
  · change eval rho []=eval rho [(33772,1)]
    simp only [eval,Int.cast_one,one_mul,add_zero]
    rw [pr.2,meaning,flag,FieldZeroSeed125.annihilated]
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.truth
#print axioms ShielddSecurity.CapturedHighZero126.truth
theorem complete (rho : Nat → F) (d : F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (meaning : eval rho delta=d) (flag : rho 1110=FieldZeroSeed125.flag d)
    (inverse : rho 1111=d⁻¹) (one : rho 0=1) (linked : rho copy=rho 0) :
    SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (179023+index)) 3 := by
  have h:=(satisfies_iff copy 3 block rho linked).mpr (truth rho d arithmetic meaning flag inverse one)
  intro index bound row found
  exact h index bound row ((assertion_position index bound).symm.trans found)
set_option pp.all true in
#check @ShielddSecurity.CapturedHighZero126.complete
#print axioms ShielddSecurity.CapturedHighZero126.complete
end ShielddSecurity.CapturedHighZero126
