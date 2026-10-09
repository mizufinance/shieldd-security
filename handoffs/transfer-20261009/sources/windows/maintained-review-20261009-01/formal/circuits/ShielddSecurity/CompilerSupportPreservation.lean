import ShielddSecurity.CompilerCompletion

set_option maxHeartbeats 300000

namespace ShielddSecurity.CompilerSupportPreservation

variable {F : Type} [Field F]

/-- A prior row's actual support is protected at every subsequent compiler
stage. This derives column preservation even when the column is not listed as
an externally owned caller input. No prior row satisfaction is required. -/
theorem run_support (base : Nat → F) (stages : List CompilerCompletion.Step)
    (kept : List Nat) (prior : List Row)
    (ordered : CompilerCompletion.Topological kept prior stages)
    (row : Row) (member : row ∈ prior) (term : Nat × Int) (present : term ∈ row.a ++ row.b) :
    CompilerCompletion.run base stages term.1 = base term.1 := by
  induction stages generalizing base prior with
  | nil => rfl
  | cons stage tail ih =>
      exact (ih (stage.run base) (prior ++ stage.rows) ordered.2.2.2
        (List.mem_append_left stage.rows member)).trans
        (CompilerCompletion.step_preserves stage base term.1 (ordered.2.2.1 row member term present))

theorem run_eval_support (base : Nat → F) (stages : List CompilerCompletion.Step)
    (kept : List Nat) (prior : List Row)
    (ordered : CompilerCompletion.Topological kept prior stages)
    (row : Row) (member : row ∈ prior) (terms : Linear)
    (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
    eval (CompilerCompletion.run base stages) terms = eval base terms := by
  apply eval_agrees
  intro term present
  exact run_support base stages kept prior ordered row member term (inside term present)

set_option pp.all true in
#check @run_support
#print axioms run_support
set_option pp.all true in
#check @run_eval_support
#print axioms run_eval_support

end ShielddSecurity.CompilerSupportPreservation
