import ShielddSecurity.CapturedAssertions50B0001
import ShielddSecurity.CapturedAssertions50B0002
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryAssetRange109
open CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def columns : List Nat := List.range' 471 255
noncomputable def expected (index : Nat) : Recipe :=
  if index<255 then .square [(471+index,1)] [(471+index,1)]
  else .linear (weighted columns 1) [(6,1)]
def sameRecipe : Recipe → Recipe → Bool
  | .linear a b,.linear c d | .square a b,.square c d => decide (a=c ∧ b=d)
  | _,_ => false
theorem sameRecipe_sound (left right : Recipe) (checked : sameRecipe left right=true) : left=right := by
  cases left <;> cases right <;> simp only [sameRecipe,decide_eq_true_eq,Bool.false_eq_true] at checked
  all_goals first
    | contradiction
    | rcases checked with ⟨rfl,rfl⟩;rfl
noncomputable def block : Block p copy 256 where
  actual := fun index => if index<89 then CapturedAssertions50B0001.block.actual (167+index)
    else CapturedAssertions50B0002.block.actual (index-89)
  recipe := fun index => if index<89 then CapturedAssertions50B0001.block.recipe (167+index)
    else CapturedAssertions50B0002.block.recipe (index-89)
  exact_checked := by
    intro index bound
    by_cases before : index<89
    · simpa only [before,if_true] using CapturedAssertions50B0001.block.exact_checked (167+index) (show 167+index<256 by omega)
    · simpa only [before,if_false] using CapturedAssertions50B0002.block.exact_checked (index-89) (show index-89<256 by omega)
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
end ShielddSecurity.CapturedRegistryAssetRange109
