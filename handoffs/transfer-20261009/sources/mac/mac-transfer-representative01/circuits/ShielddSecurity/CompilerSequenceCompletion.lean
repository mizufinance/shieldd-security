import ShielddSecurity.PoseidonCompletion

set_option maxHeartbeats 150000

namespace ShielddSecurity.CompilerSequenceCompletion

variable {F : Type} [Field F]

theorem run_append (base : Nat → F) (first second : List CompilerCompletion.Step) :
    CompilerCompletion.run base (first ++ second) =
      CompilerCompletion.run (CompilerCompletion.run base first) second := by
  induction first generalizing base with
  | nil => rfl
  | cons step tail ih =>
      simpa only [List.cons_append,CompilerCompletion.run] using ih (step.run base)

theorem preserves_rows (base : Nat → F) (steps : List CompilerCompletion.Step)
    (rows : List Row) (completed : Satisfies base rows)
    (outside : ∀ row ∈ rows, ∀ term ∈ row.a ++ row.b,
      term.1 ∉ PoseidonCompletion.writes steps) :
    Satisfies (CompilerCompletion.run base steps) rows := by
  intro row member
  rw [PoseidonCompletion.eval_run_preserves base steps row.a
        (by intro term present; exact outside row member term (List.mem_append_left _ present)),
      PoseidonCompletion.eval_run_preserves base steps row.b
        (by intro term present; exact outside row member term (List.mem_append_right _ present))]
  exact completed row member

/-- A few deferred inverse auxiliaries may be below the ordinary allocation
floor. They are checked separately, rather than widening the protected frame
to a false interval or comparing every earlier term with every later write. -/
def checkWrites (copy floor : Nat) (exceptions writes : List Nat) : Bool :=
  writes.all (fun column => decide (column ≠ copy ∧ (floor ≤ column ∨ column ∈ exceptions)))

def checkRows (copy floor : Nat) (exceptions : List Nat) (rows : List Row) : Bool :=
  rows.all (fun row => (row.a ++ row.b).all (fun term =>
    decide ((term.1 = copy ∨ term.1 < floor) ∧ term.1 ∉ exceptions)))

theorem frame_column (copy floor : Nat) (exceptions writes : List Nat) (column : Nat)
    (checked : checkWrites copy floor exceptions writes = true)
    (covered : (column = copy ∨ column < floor) ∧ column ∉ exceptions) : column ∉ writes := by
  intro member
  have written := of_decide_eq_true (List.all_eq_true.mp checked column member)
  rcases covered.1 with fixed | below
  · exact written.1 fixed
  · rcases written.2 with above | exceptional
    · exact (Nat.not_lt_of_ge above) below
    · exact covered.2 exceptional

theorem frame_rows (copy floor : Nat) (exceptions writes : List Nat) (rows : List Row)
    (lower : checkWrites copy floor exceptions writes = true)
    (upper : checkRows copy floor exceptions rows = true) :
    ∀ row ∈ rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ writes := by
  intro row member term present
  exact frame_column copy floor exceptions writes term.1 lower
    (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp upper row member) term present))

set_option pp.all true in
#check @run_append
#print axioms run_append
set_option pp.all true in
#check @preserves_rows
#print axioms preserves_rows
set_option pp.all true in
#check @frame_column
#print axioms frame_column
set_option pp.all true in
#check @frame_rows
#print axioms frame_rows

end ShielddSecurity.CompilerSequenceCompletion
