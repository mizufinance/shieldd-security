import ShielddSecurity.CompilerOrder

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

namespace ShielddSecurity.CompilerOrderComposition

theorem extend (kept : List Nat) (prior extra : List Row) (steps : List CompilerCompletion.Step)
    (ordered : CompilerCompletion.Topological kept prior steps)
    (fresh : ∀ row ∈ extra, ∀ term ∈ row.a ++ row.b, ∀ step ∈ steps, term.1 ∉ step.writes) :
    CompilerCompletion.Topological kept (extra ++ prior) steps := by
  induction steps generalizing prior with
  | nil => trivial
  | cons step tail ih =>
      refine ⟨ordered.1, ordered.2.1, ?_, ?_⟩
      · intro row member term present
        rcases List.mem_append.mp member with member | member
        · exact fresh row member term present step List.mem_cons_self
        · exact ordered.2.2.1 row member term present
      · simpa only [List.append_assoc] using ih (prior ++ step.rows) ordered.2.2.2
          (by intro row member term present next found
              exact fresh row member term present next (List.mem_cons_of_mem step found))

theorem append (kept : List Nat) (prior : List Row) (first second : List CompilerCompletion.Step)
    (firstOrder : CompilerCompletion.Topological kept prior first)
    (secondOrder : CompilerCompletion.Topological kept (prior ++ CompilerCompletion.emitted first) second) :
    CompilerCompletion.Topological kept prior (first ++ second) := by
  induction first generalizing prior with
  | nil => simpa only [List.nil_append, CompilerCompletion.emitted, List.append_nil] using secondOrder
  | cons step tail ih =>
      refine ⟨firstOrder.1, firstOrder.2.1, firstOrder.2.2.1, ?_⟩
      apply ih (prior ++ step.rows) firstOrder.2.2.2
      simpa only [CompilerCompletion.emitted, List.append_assoc] using secondOrder

private theorem shape_checked (step : CompilerCompletion.Step) (shape : step.Shape) :
    CompilerOrder.checkShape step = true := by
  cases step with
  | square input remainder output =>
      apply List.all_eq_true.mpr
      intro term member
      apply decide_eq_true
      simpa only [List.mem_singleton] using shape term member
  | product left right remainder output auxiliary =>
      simp only [CompilerOrder.checkShape, Bool.and_eq_true]
      refine ⟨decide_eq_true shape.1, ?_⟩
      apply List.all_eq_true.mpr
      intro term member
      exact decide_eq_true (shape.2 term member)
  | equal left right => rfl
  | squareEqual input target => rfl

/-- Numeric instance certificates may be split into small chunks; their
symbolic Topological composition supplies the original Boolean conclusion
without reducing one large cartesian support walk in the kernel. -/
theorem check_order (kept : List Nat) (prior : List Row) (steps : List CompilerCompletion.Step)
    (ordered : CompilerCompletion.Topological kept prior steps) :
    CompilerOrder.checkOrder kept prior steps = true := by
  induction steps generalizing prior with
  | nil => rfl
  | cons step tail ih =>
      simp only [CompilerOrder.checkOrder, Bool.and_eq_true]
      refine ⟨⟨⟨shape_checked step ordered.1, ?_⟩, ?_⟩, ih _ ordered.2.2.2⟩
      · apply List.all_eq_true.mpr
        intro column written
        exact decide_eq_true (fun member => ordered.2.1 column member written)
      · apply List.all_eq_true.mpr
        intro row member
        apply List.all_eq_true.mpr
        intro term present
        exact decide_eq_true (ordered.2.2.1 row member term present)

set_option pp.all true in
#check @extend
#print axioms extend
set_option pp.all true in
#check @append
#print axioms append
set_option pp.all true in
#check @check_order
#print axioms check_order

end ShielddSecurity.CompilerOrderComposition
