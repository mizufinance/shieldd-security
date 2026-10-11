import ShielddSecurity.CapturedNextHighShared136
import ShielddSecurity.FieldZeroSeed125
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedNextHighZero137Data
import ShielddSecurity.CapturedArithmetic45B0048
import ShielddSecurity.CapturedAssertions50B0005
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedNextHighZero138
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def delta : Linear := weighted CapturedNextHighLimb133.rightColumns (-1)++weighted CapturedNextHighLimb133.leftColumns 1
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.delta
#print axioms ShielddSecurity.CapturedNextHighZero138.delta
noncomputable def arithmeticRows : List Row := CapturedNextHighZero137Data.arithmeticRows
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.arithmeticRows
#print axioms ShielddSecurity.CapturedNextHighZero138.arithmeticRows
noncomputable def actualRows : List Row := CapturedNextHighZero137Data.actualRows
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.actualRows
#print axioms ShielddSecurity.CapturedNextHighZero138.actualRows
noncomputable def arithmeticCheck : Bool := CapturedNextHighZero137Data.arithmeticCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.arithmeticCheck
#print axioms ShielddSecurity.CapturedNextHighZero138.arithmeticCheck
theorem arithmetic_checked : arithmeticCheck=true := CapturedNextHighZero137Data.arithmetic_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.arithmetic_checked
#print axioms ShielddSecurity.CapturedNextHighZero138.arithmetic_checked
noncomputable def assertionCheck : Bool := CapturedNextHighZero137Data.assertionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.assertionCheck
#print axioms ShielddSecurity.CapturedNextHighZero138.assertionCheck
theorem assertion_checked : assertionCheck=true := CapturedNextHighZero137Data.assertion_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.assertion_checked
#print axioms ShielddSecurity.CapturedNextHighZero138.assertion_checked
noncomputable def inverseCheck : Bool := Compiler.checkRow p arithmeticRows ⟨subtract delta [(1372,1)],[(33779,1)]⟩ &&
  Compiler.checkRow p arithmeticRows ⟨delta++[(1372,1)],[(33779,1)]++scaleLinear 4 [(33778,1)]⟩
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.inverseCheck
#print axioms ShielddSecurity.CapturedNextHighZero138.inverseCheck
theorem inverse_checked : inverseCheck=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.inverse_checked
#print axioms ShielddSecurity.CapturedNextHighZero138.inverse_checked
noncomputable def zeroCheck : Bool := Compiler.checkRow p arithmeticRows ⟨subtract delta [(1371,1)],[(33781,1)]⟩ &&
  Compiler.checkRow p arithmeticRows ⟨delta++[(1371,1)],[(33781,1)]++scaleLinear 4 [(33780,1)]⟩
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.zeroCheck
#print axioms ShielddSecurity.CapturedNextHighZero138.zeroCheck
theorem zero_checked : zeroCheck=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.zero_checked
#print axioms ShielddSecurity.CapturedNextHighZero138.zero_checked
def expected (index : Nat) : Recipe :=
  if index=0 then .square [(1371,1)] [(1371,1)]
  else if index=1 then .linear [(33778,1),(1371,1)] [(0,1)]
  else .linear [] [(33780,1)]
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.expected
#print axioms ShielddSecurity.CapturedNextHighZero138.expected
noncomputable def productionCheck : Bool := (List.range 3).all (fun index =>
  match actualRows[index]? with
  | some row => CompilerAssertionBlock51.checkRow p copy row (true,expected index)
  | none => false)
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.productionCheck
#print axioms ShielddSecurity.CapturedNextHighZero138.productionCheck
theorem production_checked : productionCheck=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.production_checked
#print axioms ShielddSecurity.CapturedNextHighZero138.production_checked
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
#check @ShielddSecurity.CapturedNextHighZero138.block
#print axioms ShielddSecurity.CapturedNextHighZero138.block
theorem hint_exact (index : Nat) (hint : Bool × Recipe) (found : block.recipe index=some hint) :
    hint.2=expected index := by
  change some (true,expected index)=some hint at found
  exact congrArg Prod.snd (Option.some.inj found).symm
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.hint_exact
#print axioms ShielddSecurity.CapturedNextHighZero138.hint_exact
theorem arithmetic_position (index : Nat) (bound : index<4) :
    CapturedFullArithmetic52.rowAt (11040+index)=arithmeticRows[index]? :=
  CapturedNextHighZero137Data.arithmetic_position index bound
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.arithmetic_position
#print axioms ShielddSecurity.CapturedNextHighZero138.arithmetic_position
theorem assertion_position (index : Nat) (bound : index<3) :
    CapturedFullRelation58.rowAt (179287+index)=actualRows[index]? :=
  CapturedNextHighZero137Data.assertion_position index bound
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.assertion_position
#print axioms ShielddSecurity.CapturedNextHighZero138.assertion_position
variable {F : Type} [Field F] [CharP F p]
theorem products (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 33778=eval rho delta*rho 1372 ∧ rho 33780=eval rho delta*rho 1371 := by
  have sat : Satisfies rho arithmeticRows := by
    intro row member
    obtain ⟨index,found⟩:=List.mem_iff_getElem?.mp member
    obtain ⟨before,_⟩:=List.getElem?_eq_some_iff.mp found
    have bound : index<4 := by
      rw [CompilerRowSlice63.count CapturedArithmetic45B0048.block.actual 448 4 arithmeticRows arithmetic_checked] at before
      exact before
    exact arithmetic (11040+index) (by omega) row ((arithmetic_position index bound).trans found)
  have hi:=checked_product_sound rho arithmeticRows delta [(1372,1)] [(33778,1)] [(33779,1)]
    four_ne_zero sat (Bool.and_eq_true_iff.mp inverse_checked).1 (Bool.and_eq_true_iff.mp inverse_checked).2
  have hz:=checked_product_sound rho arithmeticRows delta [(1371,1)] [(33780,1)] [(33781,1)]
    four_ne_zero sat (Bool.and_eq_true_iff.mp zero_checked).1 (Bool.and_eq_true_iff.mp zero_checked).2
  constructor
  · simpa only [eval,Int.cast_one,one_mul,add_zero] using hi
  · simpa only [eval,Int.cast_one,one_mul,add_zero] using hz
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.products
#print axioms ShielddSecurity.CapturedNextHighZero138.products
theorem truth (rho : Nat → F) (d : F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (meaning : eval rho delta=d) (flag : rho 1371=FieldZeroSeed125.flag d)
    (inverse : rho 1372=d⁻¹) (one : rho 0=1) : TruthAt rho block.recipe 3 := by
  have pr:=products rho arithmetic
  intro index bound hint found
  rw [hint_exact index hint found]
  have cases : index=0 ∨ index=1 ∨ index=2 := by omega
  rcases cases with rfl | rfl | rfl
  · change Square (eval rho [(1371,1)]) (eval rho [(1371,1)])
    simpa only [eval,Int.cast_one,one_mul,add_zero,flag] using FieldZeroSeed125.boolean d
  · change eval rho [(33778,1),(1371,1)]=eval rho [(0,1)]
    simp only [eval,Int.cast_one,one_mul,add_zero]
    rw [pr.1,meaning,inverse,flag,one,FieldZeroSeed125.inverse]
    ring
  · change eval rho []=eval rho [(33780,1)]
    simp only [eval,Int.cast_one,one_mul,add_zero]
    rw [pr.2,meaning,flag,FieldZeroSeed125.annihilated]
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.truth
#print axioms ShielddSecurity.CapturedNextHighZero138.truth
theorem complete (rho : Nat → F) (d : F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (meaning : eval rho delta=d) (flag : rho 1371=FieldZeroSeed125.flag d)
    (inverse : rho 1372=d⁻¹) (one : rho 0=1) (linked : rho copy=rho 0) :
    SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (179287+index)) 3 := by
  have h:=(satisfies_iff copy 3 block rho linked).mpr (truth rho d arithmetic meaning flag inverse one)
  intro index bound row found
  exact h index bound row ((assertion_position index bound).symm.trans found)
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighZero138.complete
#print axioms ShielddSecurity.CapturedNextHighZero138.complete
end ShielddSecurity.CapturedNextHighZero138
