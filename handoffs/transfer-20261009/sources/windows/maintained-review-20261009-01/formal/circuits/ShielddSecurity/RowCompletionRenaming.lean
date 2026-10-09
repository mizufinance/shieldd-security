import ShielddSecurity.RowRenaming

set_option maxHeartbeats 200000
set_option maxRecDepth 2048

namespace ShielddSecurity.RowCompletionRenaming

/-- Transport only a constructor's explicitly owned writes. The inverse needs
to be correct on the finite row support and owned set, not on all Nat columns. -/
def assignment {F : Type} (base constructed : Nat → F) (columns inverse : Nat → Nat)
    (writes : List Nat) : Nat → F :=
  fun column => if column ∈ writes.map columns then constructed (inverse column) else base column

theorem assignment_preserves {F : Type} (base constructed : Nat → F)
    (columns inverse : Nat → Nat) (writes : List Nat) (column : Nat)
    (outside : column ∉ writes.map columns) :
    assignment base constructed columns inverse writes column = base column := by
  simp only [assignment, if_neg outside]

theorem assignment_at {F : Type} (base constructed : Nat → F)
    (columns inverse : Nat → Nat) (writes : List Nat) (column : Nat)
    (inverted : inverse (columns column) = column)
    (invertedWrites : ∀ item ∈ writes, inverse (columns item) = item)
    (preserved : ∀ item, item ∉ writes → constructed item = base (columns item)) :
    assignment base constructed columns inverse writes (columns column) = constructed column := by
  by_cases member : columns column ∈ writes.map columns
  · simp only [assignment, if_pos member, inverted]
  · have outside : column ∉ writes := by
      intro present
      exact member (List.mem_map.mpr ⟨column, present, rfl⟩)
    rw [preserved column outside]
    exact assignment_preserves base constructed columns inverse writes (columns column) member

/-- The source satisfaction is discharged by an existing constructive theorem
at each instance. Exact finite row equality and inverse checks are separate
certificates; neither a desired actual state nor actual row satisfaction is an
input to this transport. -/
theorem complete_rows {F : Type} [Field F] (base constructed : Nat → F)
    (columns inverse : Nat → Nat) (writes : List Nat) (source actual : List Row)
    (exactRows : actual = source.map (RowRenaming.row columns))
    (invertedRows : ∀ item ∈ source, ∀ term ∈ item.a ++ item.b,
      inverse (columns term.1) = term.1)
    (invertedWrites : ∀ item ∈ writes, inverse (columns item) = item)
    (preserved : ∀ item, item ∉ writes → constructed item = base (columns item))
    (completed : Satisfies constructed source) :
    Satisfies (assignment base constructed columns inverse writes) actual := by
  intro item member
  rw [exactRows] at member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  have agrees (terms : Linear) (included : ∀ term ∈ terms, term ∈ original.a ++ original.b) :
      eval (assignment base constructed columns inverse writes) (RowRenaming.linear columns terms) =
        eval constructed terms := by
    rw [RowRenaming.eval_linear]
    apply eval_agrees
    intro term found
    exact assignment_at base constructed columns inverse writes term.1
      (invertedRows original present term (included term found)) invertedWrites preserved
  change Square
    (eval (assignment base constructed columns inverse writes) (RowRenaming.linear columns original.a))
    (eval (assignment base constructed columns inverse writes) (RowRenaming.linear columns original.b))
  rw [agrees original.a (by intro term found; exact List.mem_append_left original.b found),
      agrees original.b (by intro term found; exact List.mem_append_right original.a found)]
  exact completed original present

theorem eval_preserves {F : Type} [Field F] (base constructed : Nat → F)
    (columns inverse : Nat → Nat) (writes : List Nat) (terms : Linear)
    (outside : ∀ term ∈ terms, term.1 ∉ writes.map columns) :
    eval (assignment base constructed columns inverse writes) terms = eval base terms := by
  apply eval_agrees
  intro term member
  exact assignment_preserves base constructed columns inverse writes term.1 (outside term member)

set_option pp.all true in
#check @assignment_preserves
#print axioms assignment_preserves
set_option pp.all true in
#check @assignment_at
#print axioms assignment_at
set_option pp.all true in
#check @complete_rows
#print axioms complete_rows
set_option pp.all true in
#check @eval_preserves
#print axioms eval_preserves

end ShielddSecurity.RowCompletionRenaming
