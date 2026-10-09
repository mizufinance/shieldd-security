import ShielddSecurity.ScalarRandomizerBounds
import ShielddSecurity.PoseidonCompletion

set_option maxHeartbeats 150000

namespace ShielddSecurity.ScalarProductWriteLowerBound

/-- Reuse the checked product allocation bounds without evaluating the program. -/
theorem bounded_writes (lower upper : Nat) (stages : List CompilerCompletion.Step)
    (checked : ScalarRandomizerBounds.checkBounded lower upper stages = true) :
    ∀ column ∈ PoseidonCompletion.writes stages, lower ≤ column := by
  induction stages generalizing lower with
  | nil => simp [PoseidonCompletion.writes]
  | cons stage tail ih =>
      cases stage with
      | square input remainder output => simp [ScalarRandomizerBounds.checkBounded] at checked
      | equal left right => simp [ScalarRandomizerBounds.checkBounded] at checked
      | squareEqual input target => simp [ScalarRandomizerBounds.checkBounded] at checked
      | product left right remainder output auxiliary =>
          simp only [ScalarRandomizerBounds.checkBounded, Bool.and_eq_true,
            decide_eq_true_eq] at checked
          intro column member
          simp only [PoseidonCompletion.writes, List.flatMap_cons, List.mem_append] at member
          rcases member with now | later
          · simp only [CompilerCompletion.Step.writes, List.mem_cons,
              List.not_mem_nil, or_false] at now
            rcases now with rfl | rfl <;> omega
          · have remaining := ih (auxiliary + 1) checked.2 column later
            omega

theorem append_writes (bound : Nat) (left right : List CompilerCompletion.Step)
    (first : ∀ column ∈ PoseidonCompletion.writes left, bound ≤ column)
    (second : ∀ column ∈ PoseidonCompletion.writes right, bound ≤ column) :
    ∀ column ∈ PoseidonCompletion.writes (left ++ right), bound ≤ column := by
  intro column member
  simp only [PoseidonCompletion.writes, List.flatMap_append, List.mem_append] at member
  rcases member with before | after
  · exact first column before
  · exact second column after

set_option pp.all true in
#check @bounded_writes
#print axioms bounded_writes
set_option pp.all true in
#check @append_writes
#print axioms append_writes

end ShielddSecurity.ScalarProductWriteLowerBound
