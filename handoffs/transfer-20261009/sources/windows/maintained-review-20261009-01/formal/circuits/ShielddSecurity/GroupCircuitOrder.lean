import ShielddSecurity.GroupCircuitCompletion

set_option maxHeartbeats 500000

namespace ShielddSecurity.GroupCircuitOrder

def checkOutside (columns : List Nat) (writes : List Nat) : Bool :=
  writes.all (fun column => decide (column ∉ columns))

private theorem checked_outside (columns writes : List Nat)
    (checked : checkOutside columns writes = true) :
    ∀ column ∈ columns, column ∉ writes := by
  intro column member written
  exact (of_decide_eq_true (List.all_eq_true.mp checked column written)) member

def checkTerms (terms : Linear) (writes : List Nat) : Bool :=
  terms.all (fun term => decide (term.1 ∉ writes))

private theorem checked_terms (terms : Linear) (writes : List Nat)
    (checked : checkTerms terms writes = true) :
    ∀ term ∈ terms, term.1 ∉ writes := by
  intro term member
  exact of_decide_eq_true (List.all_eq_true.mp checked term member)

def checkShape : GroupCircuitCompletion.Step → Bool
  | .compiler (.square input remainder output) => checkTerms (input ++ remainder) [output]
  | .compiler (.product left right remainder output auxiliary) =>
      decide (output ≠ auxiliary) && checkTerms (left ++ right ++ remainder) [output, auxiliary]
  | .compiler (.equal _ _) | .compiler (.squareEqual _ _) => true
  | .quotient numerator denominator remainder output product auxiliary =>
      decide (output ≠ product ∧ output ≠ auxiliary ∧ product ≠ auxiliary) &&
        checkTerms (numerator ++ denominator ++ remainder) [output, product, auxiliary]
  | .linear input remainder output => checkTerms (input ++ remainder) [output]

theorem checked_shape (step : GroupCircuitCompletion.Step)
    (checked : checkShape step = true) : step.Shape := by
  cases step with
  | compiler step =>
      cases step with
      | square input remainder output =>
          intro term member
          simpa only [List.mem_singleton] using checked_terms _ _ checked term member
      | product left right remainder output auxiliary =>
          simp only [checkShape, Bool.and_eq_true, decide_eq_true_eq] at checked
          exact ⟨checked.1, checked_terms _ _ checked.2⟩
      | equal left right => trivial
      | squareEqual input target => trivial
  | quotient numerator denominator remainder output product auxiliary =>
      simp only [checkShape, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact ⟨checked.1.1, checked.1.2.1, checked.1.2.2, checked_terms _ _ checked.2⟩
  | linear input remainder output =>
      intro term member
      simpa only [List.mem_singleton] using checked_terms _ _ checked term member

/-- A bounded structural certificate; no row satisfaction or output value is
checked. Caller ownership is scanned once per write, rather than expanded by
the simplifier into thousands of repeated membership alternatives. -/
def checkOrder (kept : List Nat) (prior : List Row) : List GroupCircuitCompletion.Step → Bool
  | [] => true
  | step :: tail => checkShape step && checkOutside kept step.writes &&
      prior.all (fun row => checkTerms (row.a ++ row.b) step.writes) &&
      checkOrder kept (prior ++ step.rows) tail

theorem checked_order (kept : List Nat) (prior : List Row)
    (steps : List GroupCircuitCompletion.Step)
    (checked : checkOrder kept prior steps = true) :
    GroupCircuitCompletion.Topological kept prior steps := by
  induction steps generalizing prior with
  | nil => trivial
  | cons step tail ih =>
      simp only [checkOrder, Bool.and_eq_true] at checked
      refine ⟨checked_shape step checked.1.1.1,
        checked_outside kept step.writes checked.1.1.2, ?_,
        ih _ checked.2⟩
      intro row member
      exact checked_terms _ _ (List.all_eq_true.mp checked.1.2 row member)

theorem run_outside {F : Type} [Field F] (base : Nat → F)
    (steps : List GroupCircuitCompletion.Step) (column : Nat)
    (outside : ∀ step ∈ steps, column ∉ step.writes) :
    GroupCircuitCompletion.run base steps column = base column := by
  induction steps generalizing base with
  | nil => rfl
  | cons step tail ih =>
      exact (ih (step.run base)
        (by intro next member; exact outside next (List.mem_cons_of_mem _ member))).trans
        (GroupCircuitCompletion.step_preserves step base column (outside step (by simp)))

set_option pp.all true in
#check @checked_shape
#print axioms checked_shape
set_option pp.all true in
#check @checked_order
#print axioms checked_order
set_option pp.all true in
#check @run_outside
#print axioms run_outside

end ShielddSecurity.GroupCircuitOrder
