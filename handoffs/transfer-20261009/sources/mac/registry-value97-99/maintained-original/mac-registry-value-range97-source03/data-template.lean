import ShielddSecurity.CapturedAssertions50B0000
import ShielddSecurity.CapturedAssertions50B0001
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryValueRange97
open CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def columns : List Nat := List.range' 216 255
noncomputable def expected (index : Nat) : Recipe :=
  if index<255 then .square [(216+index,1)] [(216+index,1)]
  else .linear (weighted columns 1) [(11,1)]
def sameRecipe : Recipe → Recipe → Bool
  | .linear a b,.linear c d | .square a b,.square c d => decide (a=c ∧ b=d)
  | _,_ => false
theorem sameRecipe_sound (left right : Recipe) (checked : sameRecipe left right=true) : left=right := by
  cases left <;> cases right <;> simp only [sameRecipe,decide_eq_true_eq,Bool.false_eq_true] at checked
  all_goals first
    | contradiction
    | rcases checked with ⟨rfl,rfl⟩;rfl
noncomputable def block : Block p copy 256 where
  actual := fun index => if index<91 then CapturedAssertions50B0000.block.actual (165+index)
    else CapturedAssertions50B0001.block.actual (index-91)
  recipe := fun index => if index<91 then CapturedAssertions50B0000.block.recipe (165+index)
    else CapturedAssertions50B0001.block.recipe (index-91)
  exact_checked := by
    intro index bound
    by_cases before : index<91
    · simpa only [before,if_true] using CapturedAssertions50B0000.block.exact_checked (165+index) (show 165+index<256 by omega)
    · simpa only [before,if_false] using CapturedAssertions50B0001.block.exact_checked (index-91) (show index-91<256 by omega)
noncomputable def productionCheck : Bool :=
  (List.range 256).all (fun index => match block.recipe index with
    | some hint => sameRecipe hint.2 (expected index)
    | none => false)
theorem production_checked : productionCheck=true := by decide +kernel
theorem recipes_exact (index : Nat) (bound : index<256) (hint : Bool × Recipe)
    (found : block.recipe index=some hint) : hint.2=expected index := by
  have checked:=List.all_eq_true.mp production_checked index (List.mem_range.mpr bound)
  rw [found] at checked
  exact sameRecipe_sound hint.2 (expected index) checked
end ShielddSecurity.CapturedRegistryValueRange97
