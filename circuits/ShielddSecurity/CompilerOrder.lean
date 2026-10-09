import ShielddSecurity.CompilerCompletion

set_option maxHeartbeats 200000

namespace ShielddSecurity.CompilerOrder

def checkTerms (terms : Linear) (writes : List Nat) : Bool :=
  terms.all (fun term => decide (term.1 ∉ writes))

private theorem checked_terms (terms : Linear) (writes : List Nat)
    (checked : checkTerms terms writes = true) : ∀ term ∈ terms, term.1 ∉ writes := by
  intro term member
  exact of_decide_eq_true (List.all_eq_true.mp checked term member)

def checkShape : CompilerCompletion.Step → Bool
  | .square input remainder output => checkTerms (input ++ remainder) [output]
  | .product left right remainder output auxiliary =>
      decide (output ≠ auxiliary) && checkTerms (left ++ right ++ remainder) [output,auxiliary]
  | .equal _ _ | .squareEqual _ _ => true

theorem checked_shape (step : CompilerCompletion.Step) (checked : checkShape step = true) :
    step.Shape := by
  cases step with
  | square input remainder output =>
      intro term member
      simpa only [List.mem_singleton] using checked_terms _ _ checked term member
  | product left right remainder output auxiliary =>
      simp only [checkShape,Bool.and_eq_true,decide_eq_true_eq] at checked
      exact ⟨checked.1,checked_terms _ _ checked.2⟩
  | equal left right => trivial
  | squareEqual input target => trivial

/-- Finite support certificates scan retained columns once per actual write.
This checks freshness and preservation only; assertion meanings remain Legal. -/
def checkOrder (kept : List Nat) (prior : List Row) : List CompilerCompletion.Step → Bool
  | [] => true
  | step :: tail => checkShape step && step.writes.all (fun column => decide (column ∉ kept)) &&
      prior.all (fun row => checkTerms (row.a ++ row.b) step.writes) &&
      checkOrder kept (prior ++ step.rows) tail

theorem checked_order (kept : List Nat) (prior : List Row) (steps : List CompilerCompletion.Step)
    (checked : checkOrder kept prior steps = true) : CompilerCompletion.Topological kept prior steps := by
  induction steps generalizing prior with
  | nil => trivial
  | cons step tail ih =>
      simp only [checkOrder,Bool.and_eq_true] at checked
      refine ⟨checked_shape step checked.1.1.1,?_,?_,ih _ checked.2⟩
      · intro column member written
        exact (of_decide_eq_true (List.all_eq_true.mp checked.1.1.2 column written)) member
      · intro row member
        exact checked_terms _ _ (List.all_eq_true.mp checked.1.2 row member)

set_option pp.all true in
#check @checked_shape
#print axioms checked_shape
set_option pp.all true in
#check @checked_order
#print axioms checked_order

end ShielddSecurity.CompilerOrder
