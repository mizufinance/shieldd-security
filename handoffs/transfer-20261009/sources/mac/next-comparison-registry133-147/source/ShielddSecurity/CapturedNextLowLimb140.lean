import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CapturedAssertions50B0005
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedNextLowLimb140
open CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def columns : List Nat := List.range' 1375 128
noncomputable def leftColumns : List Nat := List.range' 726 128
noncomputable def rightColumns : List Nat := List.range' 471 128
noncomputable def expected (index : Nat) : Recipe :=
  if index<129 then .square [(if index=0 then 1373 else 1374+index,1)] [(if index=0 then 1373 else 1374+index,1)]
  else if index=129 then .linear (weighted columns 1) [(1374,1)]
  else .linear (weighted rightColumns 1++weighted leftColumns (-1)) [(1374,1),(1373,-(2^128))]
noncomputable def actual (index : Nat) : Option Row :=
  CapturedAssertions50B0005.block.actual (56+index)
noncomputable def productionCheck : Bool := (List.range 131).all (fun index =>
  match actual index with
  | some row => checkRow p copy row (true,expected index)
  | none => false)
theorem production_checked : productionCheck=true := by decide +kernel
noncomputable def block : Block p copy 131 where
  actual := actual
  recipe := fun index => some (true,expected index)
  exact_checked := by
    intro index bound
    have h:=List.all_eq_true.mp production_checked index (List.mem_range.mpr bound)
    change (match actual index with | some row => checkRow p copy row (true,expected index) | none => false)=true at h
    cases found:actual index with
    | none => simp only [found] at h;contradiction
    | some row => exact ⟨row,(true,expected index),rfl,rfl,by simpa only [found] using h⟩
theorem hint_exact (index : Nat) (hint : Bool × Recipe) (found : block.recipe index=some hint) :
    hint.2=expected index := by
  change some (true,expected index)=some hint at found
  exact congrArg Prod.snd (Option.some.inj found).symm
theorem full_position (index : Nat) (bound : index<131) :
    CapturedFullRelation58.rowAt (179290+index)=block.actual index := by
  have sum : 179290+index=177954+(1336+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (1336+index) (by omega)]
  change (if 1336+index<12288 then _ else _) = _
  rw [if_pos (show 1336+index<12288 by omega)]
  change (if 1336+index<4096 then _ else _) = _
  rw [if_pos (show 1336+index<4096 by omega)]
  change (if 1336+index<2048 then _ else _) = _
  rw [if_pos (show 1336+index<2048 by omega)]
  change (if 1336+index<1024 then _ else _) = _
  rw [if_neg (show ¬1336+index<1024 by omega)]
  change (if 1336+index-1024<512 then _ else _) = _
  rw [if_pos (show 1336+index-1024<512 by omega)]
  change (if 1336+index-1024<256 then _ else _) = _
  rw [if_neg (show ¬1336+index-1024<256 by omega)]
  have same : 1336+index-1024-256=56+index := by omega
  change CapturedAssertions50B0005.block.actual (1336+index-1024-256)=CapturedAssertions50B0005.block.actual (56+index)
  rw [same]
end ShielddSecurity.CapturedNextLowLimb140

set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb140.columns
#print axioms ShielddSecurity.CapturedNextLowLimb140.columns
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb140.leftColumns
#print axioms ShielddSecurity.CapturedNextLowLimb140.leftColumns
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb140.rightColumns
#print axioms ShielddSecurity.CapturedNextLowLimb140.rightColumns
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb140.expected
#print axioms ShielddSecurity.CapturedNextLowLimb140.expected
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb140.actual
#print axioms ShielddSecurity.CapturedNextLowLimb140.actual
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb140.productionCheck
#print axioms ShielddSecurity.CapturedNextLowLimb140.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb140.production_checked
#print axioms ShielddSecurity.CapturedNextLowLimb140.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb140.block
#print axioms ShielddSecurity.CapturedNextLowLimb140.block
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb140.hint_exact
#print axioms ShielddSecurity.CapturedNextLowLimb140.hint_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedNextLowLimb140.full_position
#print axioms ShielddSecurity.CapturedNextLowLimb140.full_position
