import ShielddSecurity.CompilerCompletion

set_option maxHeartbeats 200000

namespace ShielddSecurity.PoseidonCompletion

variable {F : Type} [Field F]

/-- Exact owned materialization columns of a finite local compiler program. -/
def writes (steps : List CompilerCompletion.Step) : List Nat :=
  steps.flatMap CompilerCompletion.Step.writes

/-- Construction preserves every other column, including future consumers
whose source LCs are not falsely presumed to have been completed already. -/
theorem run_outside (base : Nat → F) (steps : List CompilerCompletion.Step)
    (column : Nat) (outside : column ∉ writes steps) :
    CompilerCompletion.run base steps column = base column := by
  induction steps generalizing base with
  | nil => rfl
  | cons step tail ih =>
      simp only [writes, List.flatMap_cons, List.mem_append, not_or] at outside
      exact (ih (step.run base) outside.2).trans
        (CompilerCompletion.step_preserves step base column outside.1)

/-- Small source-LC preservation, instantiated by exact captured support data. -/
theorem eval_run_preserves (base : Nat → F) (steps : List CompilerCompletion.Step)
    (terms : Linear) (outside : ∀ term ∈ terms, term.1 ∉ writes steps) :
    eval (CompilerCompletion.run base steps) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact run_outside base steps term.1 (outside term member)

set_option pp.all true in
#check @run_outside
#print axioms run_outside
set_option pp.all true in
#check @eval_run_preserves
#print axioms eval_run_preserves

end ShielddSecurity.PoseidonCompletion
