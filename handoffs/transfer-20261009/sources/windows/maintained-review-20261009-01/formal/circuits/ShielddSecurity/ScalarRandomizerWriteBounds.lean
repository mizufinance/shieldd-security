import ShielddSecurity.ScalarRandomizerBounds
import ShielddSecurity.PoseidonCompletion

set_option maxHeartbeats 150000

namespace ShielddSecurity.ScalarRandomizerWriteBounds

private theorem interval (lower upper : Nat) (stages : List CompilerCompletion.Step)
    (checked : ScalarRandomizerBounds.checkBounded lower upper stages = true) :
    lower ≤ upper := by
  induction stages generalizing lower with
  | nil => simpa only [ScalarRandomizerBounds.checkBounded, decide_eq_true_eq] using checked
  | cons stage tail ih =>
      cases stage with
      | square input remainder output =>
          simp [ScalarRandomizerBounds.checkBounded] at checked
      | equal left right =>
          simp [ScalarRandomizerBounds.checkBounded] at checked
      | squareEqual input target =>
          simp [ScalarRandomizerBounds.checkBounded] at checked
      | product left right remainder output auxiliary =>
          simp only [ScalarRandomizerBounds.checkBounded, Bool.and_eq_true,
            decide_eq_true_eq] at checked
          have remaining := ih (auxiliary + 1) checked.2
          omega

/-- The existing bounded product certificate bounds every owned write.
No truth of the emitted rows is a premise. -/
theorem writes_bounds (lower upper : Nat) (stages : List CompilerCompletion.Step)
    (checked : ScalarRandomizerBounds.checkBounded lower upper stages = true) :
    ∀ column ∈ PoseidonCompletion.writes stages, lower ≤ column ∧ column < upper := by
  induction stages generalizing lower with
  | nil => intro column member; cases member
  | cons stage tail ih =>
      cases stage with
      | square input remainder output =>
          simp [ScalarRandomizerBounds.checkBounded] at checked
      | equal left right =>
          simp [ScalarRandomizerBounds.checkBounded] at checked
      | squareEqual input target =>
          simp [ScalarRandomizerBounds.checkBounded] at checked
      | product left right remainder output auxiliary =>
          simp only [ScalarRandomizerBounds.checkBounded, Bool.and_eq_true,
            decide_eq_true_eq] at checked
          intro column member
          have upperBound := interval (auxiliary + 1) upper tail checked.2
          rcases List.mem_append.mp member with current | later
          · simp only [CompilerCompletion.Step.writes, List.mem_cons,
              List.not_mem_nil, or_false] at current
            rcases current with rfl | rfl <;> omega
          · have remaining := ih (auxiliary + 1) checked.2 column later
            omega

set_option pp.all true in
#check @writes_bounds
#print axioms writes_bounds

end ShielddSecurity.ScalarRandomizerWriteBounds
