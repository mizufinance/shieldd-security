import ShielddSecurity.GroupCircuitSupportPreservation

set_option maxHeartbeats 100000

namespace ShielddSecurity.GroupFrameTransport

open GroupFixedCircuitBounds
variable {F : Type} [Field F]

/-- Reuse an established local constructor's row truth after later mixed
stages. Actual support coverage and write exclusion are independent finite
certificates; the later stage values need no desired-output premise. -/
theorem run_preserves_rows (base : Nat → F) (stages : List GroupCircuitCompletion.Step)
    (origin copy : Nat) (frame : Frame) (prior : List Row)
    (covered : RowsCovered origin copy frame prior)
    (outside : ∀ stage ∈ stages, ∀ column ∈ stage.writes, ¬ covers origin copy frame column)
    (constructed : Satisfies base prior) :
    Satisfies (GroupCircuitCompletion.run base stages) prior := by
  intro row member
  have preserved (terms : Linear) (inside : ∀ term ∈ terms, term ∈ row.a ++ row.b) :
      eval (GroupCircuitCompletion.run base stages) terms = eval base terms := by
    apply eval_agrees
    intro term present
    exact GroupCircuitSupportPreservation.covered_run_support base stages origin copy frame
      prior covered outside row member term (inside term present)
  rw [preserved row.a (by intro term present; exact List.mem_append.mpr (Or.inl present)),
    preserved row.b (by intro term present; exact List.mem_append.mpr (Or.inr present))]
  exact constructed row member

/-- Public RK and native cofactor witness patches preserve all earlier covered
rows before the actual subgroup materializations run. -/
theorem patch_preserves_rows (base values : Nat → F) (fresh : List Nat)
    (origin copy : Nat) (frame : Frame) (prior : List Row)
    (covered : RowsCovered origin copy frame prior)
    (outside : ∀ column ∈ fresh, ¬ covers origin copy frame column)
    (constructed : Satisfies base prior) :
    Satisfies (patchAssignment base values fresh) prior := by
  apply ShielddSecurity.patch_preserves_rows base values fresh prior constructed
  intro row member term present written
  exact outside term.1 written (covered row member term present)

set_option pp.all true in
#check @run_preserves_rows
#print axioms run_preserves_rows
set_option pp.all true in
#check @patch_preserves_rows
#print axioms patch_preserves_rows

end ShielddSecurity.GroupFrameTransport
