import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CapturedAssertions50B0004
import ShielddSecurity.CapturedAssertions50B0005
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedNextHighLimb133
open CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def columns : List Nat := List.range' 1244 127
noncomputable def leftColumns : List Nat := List.range' 854 127
noncomputable def rightColumns : List Nat := List.range' 599 127
noncomputable def expected (index : Nat) : Recipe :=
  if index<128 then .square [(if index=0 then 1242 else 1243+index,1)] [(if index=0 then 1242 else 1243+index,1)]
  else if index=128 then .linear (weighted columns 1) [(1243,1)]
  else .linear (weighted rightColumns 1++weighted leftColumns (-1)) [(1243,1),(1242,-(2^127))]
noncomputable def actual (index : Nat) : Option Row :=
  if index<77 then CapturedAssertions50B0004.block.actual (179+index)
  else CapturedAssertions50B0005.block.actual (index-77)
noncomputable def productionCheck : Bool := (List.range 130).all (fun index =>
  match actual index with
  | some row => checkRow p copy row (true,expected index)
  | none => false)
theorem production_checked : productionCheck=true := by decide +kernel
noncomputable def block : Block p copy 130 where
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
theorem full_position (index : Nat) (bound : index<130) :
    CapturedFullRelation58.rowAt (179157+index)=block.actual index := by
  have sum : 179157+index=177954+(1203+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (1203+index) (by omega)]
  change (if 1203+index<12288 then _ else _) = _
  rw [if_pos (show 1203+index<12288 by omega)]
  change (if 1203+index<4096 then _ else _) = _
  rw [if_pos (show 1203+index<4096 by omega)]
  change (if 1203+index<2048 then _ else _) = _
  rw [if_pos (show 1203+index<2048 by omega)]
  change (if 1203+index<1024 then _ else _) = _
  rw [if_neg (show ¬1203+index<1024 by omega)]
  change (if 1203+index-1024<512 then _ else _) = _
  rw [if_pos (show 1203+index-1024<512 by omega)]
  change (if 1203+index-1024<256 then _ else _) = _
  by_cases before : index<77
  · rw [if_pos (show 1203+index-1024<256 by omega)]
    have same : 1203+index-1024=179+index := by omega
    change CapturedAssertions50B0004.block.actual (1203+index-1024)=
      (if index<77 then CapturedAssertions50B0004.block.actual (179+index)
        else CapturedAssertions50B0005.block.actual (index-77))
    rw [if_pos before,same]
  · rw [if_neg (show ¬1203+index-1024<256 by omega)]
    have same : 1203+index-1024-256=index-77 := by omega
    change CapturedAssertions50B0005.block.actual (1203+index-1024-256)=
      (if index<77 then CapturedAssertions50B0004.block.actual (179+index)
        else CapturedAssertions50B0005.block.actual (index-77))
    rw [if_neg before,same]
end ShielddSecurity.CapturedNextHighLimb133

set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighLimb133.columns
#print axioms ShielddSecurity.CapturedNextHighLimb133.columns
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighLimb133.leftColumns
#print axioms ShielddSecurity.CapturedNextHighLimb133.leftColumns
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighLimb133.rightColumns
#print axioms ShielddSecurity.CapturedNextHighLimb133.rightColumns
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighLimb133.expected
#print axioms ShielddSecurity.CapturedNextHighLimb133.expected
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighLimb133.actual
#print axioms ShielddSecurity.CapturedNextHighLimb133.actual
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighLimb133.productionCheck
#print axioms ShielddSecurity.CapturedNextHighLimb133.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighLimb133.production_checked
#print axioms ShielddSecurity.CapturedNextHighLimb133.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighLimb133.block
#print axioms ShielddSecurity.CapturedNextHighLimb133.block
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighLimb133.hint_exact
#print axioms ShielddSecurity.CapturedNextHighLimb133.hint_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedNextHighLimb133.full_position
#print axioms ShielddSecurity.CapturedNextHighLimb133.full_position
