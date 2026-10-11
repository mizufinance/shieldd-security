import ShielddSecurity.CapturedHighLimbShared124
import ShielddSecurity.FieldZeroSeed125
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedArithmetic45B0048
import ShielddSecurity.CapturedAssertions50B0004
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedHighZero126
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def delta : Linear := weighted CapturedRegistryHighLimb120.leftColumns 1++weighted CapturedRegistryHighLimb120.rightColumns (-1)
noncomputable def arithmeticRows : List Row := @AR@
noncomputable def actualRows : List Row := @AS@
noncomputable def arithmeticCheck : Bool := CompilerRowSlice63.check CapturedArithmetic45B0048.block.actual 440 4 arithmeticRows
theorem arithmetic_checked : arithmeticCheck=true := by decide +kernel
noncomputable def assertionCheck : Bool := CompilerRowSlice63.check CapturedAssertions50B0004.block.actual 45 3 actualRows
theorem assertion_checked : assertionCheck=true := by decide +kernel
noncomputable def inverseCheck : Bool := Compiler.checkRow p arithmeticRows ⟨subtract delta [(1111,1)],[(33771,1)]⟩ &&
  Compiler.checkRow p arithmeticRows ⟨delta++[(1111,1)],[(33771,1)]++scaleLinear 4 [(33770,1)]⟩
theorem inverse_checked : inverseCheck=true := by decide +kernel
noncomputable def zeroCheck : Bool := Compiler.checkRow p arithmeticRows ⟨subtract delta [(1110,1)],[(33773,1)]⟩ &&
  Compiler.checkRow p arithmeticRows ⟨delta++[(1110,1)],[(33773,1)]++scaleLinear 4 [(33772,1)]⟩
theorem zero_checked : zeroCheck=true := by decide +kernel
def expected (index : Nat) : Recipe :=
  if index=0 then .square [(1110,1)] [(1110,1)]
  else if index=1 then .linear [(33770,1),(1110,1)] [(0,1)]
  else .linear [] [(33772,1)]
noncomputable def productionCheck : Bool := (List.range 3).all (fun index =>
  match actualRows[index]? with
  | some row => CompilerAssertionBlock51.checkRow p copy row (true,expected index)
  | none => false)
theorem production_checked : productionCheck=true := by decide +kernel
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
theorem hint_exact (index : Nat) (hint : Bool × Recipe) (found : block.recipe index=some hint) :
    hint.2=expected index := by
  change some (true,expected index)=some hint at found
  exact congrArg Prod.snd (Option.some.inj found).symm
theorem arithmetic_position (index : Nat) (bound : index<4) :
    CapturedFullArithmetic52.rowAt (11032+index)=arithmeticRows[index]? := by
  have leaf:=CompilerRowSlice63.position CapturedArithmetic45B0048.block.actual 440 4 arithmeticRows arithmetic_checked index bound
  change (if 11032+index<83708 then _ else _)=_
  rw [if_pos (show 11032+index<83708 by omega)]
  change (if 11032+index<28302 then _ else _)=_
  rw [if_pos (show 11032+index<28302 by omega)]
  change (if 11032+index<14381 then _ else _)=_
  rw [if_pos (show 11032+index<14381 by omega)]
  change (if 11032+index<6760 then _ else _)=_
  rw [if_neg (show ¬11032+index<6760 by omega)]
  change (if 11032+index-6760<3832 then _ else _)=_
  rw [if_neg (show ¬11032+index-6760<3832 by omega)]
  change (if 11032+index-6760-3832<2158 then _ else _)=_
  rw [if_pos (show 11032+index-6760-3832<2158 by omega)]
  change (if 11032+index-6760-3832<1332 then _ else _)=_
  rw [if_pos (show 11032+index-6760-3832<1332 by omega)]
  change (if 11032+index-6760-3832<924 then _ else _)=_
  rw [if_pos (show 11032+index-6760-3832<924 by omega)]
  change (if 11032+index-6760-3832<512 then _ else _)=_
  rw [if_pos (show 11032+index-6760-3832<512 by omega)]
  have same : 11032+index-6760-3832=440+index := by omega
  change CapturedArithmetic45B0048.block.actual (11032+index-6760-3832)=_
  rw [same]
  exact leaf
theorem assertion_position (index : Nat) (bound : index<3) :
    CapturedFullRelation58.rowAt (179023+index)=actualRows[index]? := by
  have sum : 179023+index=177954+(1069+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (1069+index) (by omega)]
  change (if 1069+index<12288 then _ else _)=_
  rw [if_pos (show 1069+index<12288 by omega)]
  change (if 1069+index<4096 then _ else _)=_
  rw [if_pos (show 1069+index<4096 by omega)]
  change (if 1069+index<2048 then _ else _)=_
  rw [if_pos (show 1069+index<2048 by omega)]
  change (if 1069+index<1024 then _ else _)=_
  rw [if_neg (show ¬1069+index<1024 by omega)]
  change (if 1069+index-1024<512 then _ else _)=_
  rw [if_pos (show 1069+index-1024<512 by omega)]
  change (if 1069+index-1024<256 then _ else _)=_
  rw [if_pos (show 1069+index-1024<256 by omega)]
  have same : 1069+index-1024=45+index := by omega
  change CapturedAssertions50B0004.block.actual (1069+index-1024)=_
  rw [same]
  exact CompilerRowSlice63.position CapturedAssertions50B0004.block.actual 45 3 actualRows assertion_checked index bound
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
theorem complete (rho : Nat → F) (d : F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (meaning : eval rho delta=d) (flag : rho 1110=FieldZeroSeed125.flag d)
    (inverse : rho 1111=d⁻¹) (one : rho 0=1) (linked : rho copy=rho 0) :
    SatisfiesAt rho (fun index => CapturedFullRelation58.rowAt (179023+index)) 3 := by
  have h:=(satisfies_iff copy 3 block rho linked).mpr (truth rho d arithmetic meaning flag inverse one)
  intro index bound row found
  exact h index bound row ((assertion_position index bound).symm.trans found)
end ShielddSecurity.CapturedHighZero126
