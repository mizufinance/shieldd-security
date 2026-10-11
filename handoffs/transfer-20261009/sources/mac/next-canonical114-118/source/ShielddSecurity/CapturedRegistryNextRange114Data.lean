import ShielddSecurity.CapturedAssertions50B0002
import ShielddSecurity.CapturedAssertions50B0003
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryNextRange114
open CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def columns : List Nat := List.range' 726 255

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryNextRange114.columns
#print axioms ShielddSecurity.CapturedRegistryNextRange114.columns
noncomputable def expected (index : Nat) : Recipe :=
  if index<255 then .square [(726+index,1)] [(726+index,1)]
  else .linear (weighted columns 1) [(13,1)]

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryNextRange114.expected
#print axioms ShielddSecurity.CapturedRegistryNextRange114.expected
def sameRecipe : Recipe → Recipe → Bool
  | .linear a b,.linear c d | .square a b,.square c d => decide (a=c ∧ b=d)
  | _,_ => false

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryNextRange114.sameRecipe
#print axioms ShielddSecurity.CapturedRegistryNextRange114.sameRecipe
theorem sameRecipe_sound (left right : Recipe) (checked : sameRecipe left right=true) : left=right := by
  cases left <;> cases right <;> simp only [sameRecipe,decide_eq_true_eq,Bool.false_eq_true] at checked
  all_goals first
    | contradiction
    | rcases checked with ⟨rfl,rfl⟩;rfl

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryNextRange114.sameRecipe_sound
#print axioms ShielddSecurity.CapturedRegistryNextRange114.sameRecipe_sound
noncomputable def block : Block p copy 256 where
  actual := fun index => if index<87 then CapturedAssertions50B0002.block.actual (169+index)
    else CapturedAssertions50B0003.block.actual (index-87)
  recipe := fun index => if index<87 then CapturedAssertions50B0002.block.recipe (169+index)
    else CapturedAssertions50B0003.block.recipe (index-87)
  exact_checked := by
    intro index bound
    by_cases before : index<87
    · simpa only [before,if_true] using CapturedAssertions50B0002.block.exact_checked (169+index) (show 169+index<256 by omega)
    · simpa only [before,if_false] using CapturedAssertions50B0003.block.exact_checked (index-87) (show index-87<256 by omega)

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryNextRange114.block
#print axioms ShielddSecurity.CapturedRegistryNextRange114.block
noncomputable def productionCheck : Bool :=
  (List.range 256).all (fun index => match block.recipe index with
    | some hint => sameRecipe hint.2 (expected index)
    | none => false)

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryNextRange114.productionCheck
#print axioms ShielddSecurity.CapturedRegistryNextRange114.productionCheck
theorem production_checked : productionCheck=true := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryNextRange114.production_checked
#print axioms ShielddSecurity.CapturedRegistryNextRange114.production_checked
theorem recipes_exact (index : Nat) (bound : index<256) (hint : Bool × Recipe)
    (found : block.recipe index=some hint) : hint.2=expected index := by
  have checked:=List.all_eq_true.mp production_checked index (List.mem_range.mpr bound)
  rw [found] at checked
  exact sameRecipe_sound hint.2 (expected index) checked
end ShielddSecurity.CapturedRegistryNextRange114

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryNextRange114.recipes_exact
#print axioms ShielddSecurity.CapturedRegistryNextRange114.recipes_exact
