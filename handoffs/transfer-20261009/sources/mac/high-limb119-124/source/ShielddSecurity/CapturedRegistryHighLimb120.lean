import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CapturedAssertions50B0003
import ShielddSecurity.CapturedAssertions50B0004
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryHighLimb120
open CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def columns : List Nat := List.range' 983 127
noncomputable def leftColumns : List Nat := List.range' 599 127
noncomputable def rightColumns : List Nat := List.range' 344 127
noncomputable def expected (index : Nat) : Recipe :=
  if index<128 then .square [(if index=0 then 981 else 982+index,1)] [(if index=0 then 981 else 982+index,1)]
  else if index=128 then .linear (weighted columns 1) [(982,1)]
  else .linear (weighted rightColumns 1++weighted leftColumns (-1)) [(982,1),(981,-(2^127))]
noncomputable def actual (index : Nat) : Option Row :=
  if index<85 then CapturedAssertions50B0003.block.actual (171+index)
  else CapturedAssertions50B0004.block.actual (index-85)
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
    CapturedFullRelation58.rowAt (178893+index)=block.actual index := by
  have sum : 178893+index=177954+(939+index) := by omega
  rw [sum,CapturedFullRelation58.assertion_position (939+index) (by omega)]
  have h12288 : 939+index<12288 := by omega
  have h4096 : 939+index<4096 := by omega
  have h2048 : 939+index<2048 := by omega
  change (if 939+index<12288 then _ else _) = _
  rw [if_pos h12288]
  change (if 939+index<4096 then _ else _) = _
  rw [if_pos h4096]
  change (if 939+index<2048 then _ else _) = _
  rw [if_pos h2048]
  change (if 939+index<1024 then _ else _) = _
  by_cases before : index<85
  · rw [if_pos (show 939+index<1024 by omega)]
    change (if 939+index<512 then _ else _) = _
    rw [if_neg (show ¬939+index<512 by omega)]
    change (if 939+index-512<256 then _ else _) = _
    rw [if_neg (show ¬939+index-512<256 by omega)]
    have same : 939+index-512-256=171+index := by omega
    change CapturedAssertions50B0003.block.actual (939+index-512-256)=
      (if index<85 then CapturedAssertions50B0003.block.actual (171+index)
        else CapturedAssertions50B0004.block.actual (index-85))
    rw [if_pos before,same]
  · rw [if_neg (show ¬939+index<1024 by omega)]
    change (if 939+index-1024<512 then _ else _) = _
    rw [if_pos (show 939+index-1024<512 by omega)]
    change (if 939+index-1024<256 then _ else _) = _
    rw [if_pos (show 939+index-1024<256 by omega)]
    have same : 939+index-1024=index-85 := by omega
    change CapturedAssertions50B0004.block.actual (939+index-1024)=
      (if index<85 then CapturedAssertions50B0003.block.actual (171+index)
        else CapturedAssertions50B0004.block.actual (index-85))
    rw [if_neg before,same]
end ShielddSecurity.CapturedRegistryHighLimb120

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb120.columns
#print axioms ShielddSecurity.CapturedRegistryHighLimb120.columns
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb120.leftColumns
#print axioms ShielddSecurity.CapturedRegistryHighLimb120.leftColumns
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb120.rightColumns
#print axioms ShielddSecurity.CapturedRegistryHighLimb120.rightColumns
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb120.expected
#print axioms ShielddSecurity.CapturedRegistryHighLimb120.expected
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb120.actual
#print axioms ShielddSecurity.CapturedRegistryHighLimb120.actual
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb120.productionCheck
#print axioms ShielddSecurity.CapturedRegistryHighLimb120.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb120.production_checked
#print axioms ShielddSecurity.CapturedRegistryHighLimb120.production_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb120.block
#print axioms ShielddSecurity.CapturedRegistryHighLimb120.block
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb120.hint_exact
#print axioms ShielddSecurity.CapturedRegistryHighLimb120.hint_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryHighLimb120.full_position
#print axioms ShielddSecurity.CapturedRegistryHighLimb120.full_position
