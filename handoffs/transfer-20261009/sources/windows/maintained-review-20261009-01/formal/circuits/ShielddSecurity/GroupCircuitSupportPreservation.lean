import ShielddSecurity.GroupCircuitCompletion
import ShielddSecurity.GroupFixedCircuitBounds

set_option maxHeartbeats 200000

namespace ShielddSecurity.GroupCircuitSupportPreservation

variable {F : Type} [Field F]

/-- Every mixed compiler/quotient/linear stage preserves columns it does not
write. This statement needs neither row truth nor arithmetic legality; actual
instances must establish the finite source/row support exclusion. -/
theorem run_outside (base : Nat → F) (stages : List GroupCircuitCompletion.Step)
    (column : Nat) (outside : ∀ stage ∈ stages, column ∉ stage.writes) :
    GroupCircuitCompletion.run base stages column = base column := by
  induction stages generalizing base with
  | nil => rfl
  | cons stage tail ih =>
      have later : ∀ next ∈ tail, column ∉ next.writes := by
        intro next member
        exact outside next (List.mem_cons_of_mem stage member)
      exact (ih (stage.run base) later).trans
        (GroupCircuitCompletion.step_preserves stage base column
          (outside stage (List.mem_cons_self)))

/-- Transport a bounded actual LC through the mixed stage sequence without
adding all previous row supports to the external caller list. The proof is
symbolic in the sequence and LC; finite certificates identify actual writes. -/
theorem run_eval_support (base : Nat → F) (stages : List GroupCircuitCompletion.Step)
    (terms : Linear)
    (outside : ∀ term ∈ terms, ∀ stage ∈ stages, term.1 ∉ stage.writes) :
    eval (GroupCircuitCompletion.run base stages) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact run_outside base stages term.1 (outside term member)

def finalFrame (before : GroupFixedCircuitBounds.Frame) :
    List (GroupFixedCircuitCompletion.Program × GroupFixedCircuitBounds.Frame) → GroupFixedCircuitBounds.Frame
  | [] => before
  | (_, after) :: tail => finalFrame after tail

private theorem covered_monotone (highStart copy : Nat)
    (before after : GroupFixedCircuitBounds.Frame)
    (growth : before.low ≤ after.low ∧ before.high ≤ after.high) (column : Nat)
    (covered : GroupFixedCircuitBounds.covers highStart copy before column) :
    GroupFixedCircuitBounds.covers highStart copy after column := by
  rcases covered with low | high | copied
  · exact Or.inl (Nat.lt_of_lt_of_le low growth.1)
  · exact Or.inr (Or.inl ⟨high.1,Nat.lt_of_lt_of_le high.2 growth.2⟩)
  · exact Or.inr (Or.inr copied)

/-- Reuse the existing bounded window support certificate to obtain one final
allocation frame for all preceding rows. No wide row traversal is required. -/
theorem certified_rows_covered (highStart copy : Nat) (before : GroupFixedCircuitBounds.Frame)
    (prior : List Row)
    (segments : List (GroupFixedCircuitCompletion.Program × GroupFixedCircuitBounds.Frame))
    (initial : GroupFixedCircuitBounds.RowsCovered highStart copy before prior)
    (certificate : GroupFixedCircuitBounds.Certified highStart copy before segments) :
    GroupFixedCircuitBounds.RowsCovered highStart copy (finalFrame before segments)
      (prior ++ GroupFixedCircuitCompletion.rows (segments.map Prod.fst)) := by
  induction segments generalizing before prior with
  | nil =>
      simpa only [finalFrame,List.map_nil,GroupFixedCircuitCompletion.rows,List.append_nil] using initial
  | cons segment tail ih =>
      rcases segment with ⟨program,after⟩
      rcases certificate with ⟨growth,localRows,_,remaining⟩
      have nextInitial : GroupFixedCircuitBounds.RowsCovered highStart copy after (prior ++ program.rows) := by
        intro row member term present
        rcases List.mem_append.mp member with previous | current
        · exact covered_monotone highStart copy before after growth term.1
            (initial row previous term present)
        · exact localRows row current term present
      have result := ih after (prior ++ program.rows) nextInitial remaining
      simpa only [finalFrame,List.map_cons,Prod.fst,GroupFixedCircuitCompletion.rows,List.append_assoc] using result

/-- A small final-frame exclusion for the later mixed stages protects every
earlier row support, including compiler auxiliaries absent from caller roles. -/
theorem covered_run_support (base : Nat → F) (stages : List GroupCircuitCompletion.Step)
    (highStart copy : Nat) (frame : GroupFixedCircuitBounds.Frame) (prior : List Row)
    (covered : GroupFixedCircuitBounds.RowsCovered highStart copy frame prior)
    (outside : ∀ stage ∈ stages, ∀ column ∈ stage.writes,
      ¬ GroupFixedCircuitBounds.covers highStart copy frame column)
    (row : Row) (member : row ∈ prior) (term : Nat × Int) (present : term ∈ row.a ++ row.b) :
    GroupCircuitCompletion.run base stages term.1 = base term.1 := by
  apply run_outside
  intro stage stageMember written
  exact outside stage stageMember term.1 written (covered row member term present)

set_option pp.all true in
#check @run_outside
#print axioms run_outside
set_option pp.all true in
#check @run_eval_support
#print axioms run_eval_support
set_option pp.all true in
#check @certified_rows_covered
#print axioms certified_rows_covered
set_option pp.all true in
#check @covered_run_support
#print axioms covered_run_support

end ShielddSecurity.GroupCircuitSupportPreservation
