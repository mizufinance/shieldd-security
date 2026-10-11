import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CapturedAssertions50B0004
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryLowLimb129
open CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def columns : List Nat := List.range' 1114 128
noncomputable def leftColumns : List Nat := List.range' 471 128
noncomputable def rightColumns : List Nat := List.range' 216 128
noncomputable def expected (index : Nat) : Recipe :=
  if index<129 then .square [(if index=0 then 1112 else 1113+index,1)] [(if index=0 then 1112 else 1113+index,1)]
  else if index=129 then .linear (weighted columns 1) [(1113,1)]
  else .linear (weighted rightColumns 1++weighted leftColumns (-1)) [(1113,1),(1112,-(2^128))]
noncomputable def actual (index : Nat) : Option Row :=
  CapturedAssertions50B0004.block.actual (48+index)
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
    CapturedFullRelation58.rowAt (179026+index)=block.actual index := by
  have sum : 179026+index=177954+(1072+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (1072+index) (by omega)]
  change (if 1072+index<12288 then _ else _) = _
  rw [if_pos (show 1072+index<12288 by omega)]
  change (if 1072+index<4096 then _ else _) = _
  rw [if_pos (show 1072+index<4096 by omega)]
  change (if 1072+index<2048 then _ else _) = _
  rw [if_pos (show 1072+index<2048 by omega)]
  change (if 1072+index<1024 then _ else _) = _
  rw [if_neg (show ¬1072+index<1024 by omega)]
  change (if 1072+index-1024<512 then _ else _) = _
  rw [if_pos (show 1072+index-1024<512 by omega)]
  change (if 1072+index-1024<256 then _ else _) = _
  rw [if_pos (show 1072+index-1024<256 by omega)]
  have same : 1072+index-1024=48+index := by omega
  change CapturedAssertions50B0004.block.actual (1072+index-1024)=CapturedAssertions50B0004.block.actual (48+index)
  rw [same]
end ShielddSecurity.CapturedRegistryLowLimb129
