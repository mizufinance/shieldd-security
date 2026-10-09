import ShielddSecurity.GroupCircuitOrder

set_option maxHeartbeats 150000

namespace ShielddSecurity.GroupCircuitSequenceCompletion

variable {F : Type} [Field F]

def writes (steps : List GroupCircuitCompletion.Step) : List Nat :=
  steps.flatMap GroupCircuitCompletion.Step.writes

theorem run_append (base : Nat → F) (first second : List GroupCircuitCompletion.Step) :
    GroupCircuitCompletion.run base (first ++ second) =
      GroupCircuitCompletion.run (GroupCircuitCompletion.run base first) second := by
  induction first generalizing base with
  | nil => rfl
  | cons step tail ih =>
      simpa only [List.cons_append,GroupCircuitCompletion.run] using ih (step.run base)

theorem run_preserves (base : Nat → F) (steps : List GroupCircuitCompletion.Step)
    (column : Nat) (outside : column ∉ writes steps) :
    GroupCircuitCompletion.run base steps column = base column := by
  apply GroupCircuitOrder.run_outside
  intro step member written
  exact outside (List.mem_flatMap.mpr ⟨step,member,written⟩)

theorem eval_run_preserves (base : Nat → F) (steps : List GroupCircuitCompletion.Step)
    (terms : Linear) (outside : ∀ term ∈ terms, term.1 ∉ writes steps) :
    eval (GroupCircuitCompletion.run base steps) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact run_preserves base steps term.1 (outside term member)

/-- The supplied row truth is the conclusion of an earlier local constructor.
The actual finite support exclusion lets later mixed stages retain that truth
without unfolding their computed values or assuming the final assignment. -/
theorem preserves_rows (base : Nat → F) (steps : List GroupCircuitCompletion.Step)
    (rows : List Row) (completed : Satisfies base rows)
    (outside : ∀ row ∈ rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ writes steps) :
    Satisfies (GroupCircuitCompletion.run base steps) rows := by
  intro row member
  rw [eval_run_preserves base steps row.a
        (by intro term present; exact outside row member term (List.mem_append_left _ present)),
      eval_run_preserves base steps row.b
        (by intro term present; exact outside row member term (List.mem_append_right _ present))]
  exact completed row member

set_option pp.all true in
#check @run_append
#print axioms run_append
set_option pp.all true in
#check @run_preserves
#print axioms run_preserves
set_option pp.all true in
#check @eval_run_preserves
#print axioms eval_run_preserves
set_option pp.all true in
#check @preserves_rows
#print axioms preserves_rows

end ShielddSecurity.GroupCircuitSequenceCompletion
