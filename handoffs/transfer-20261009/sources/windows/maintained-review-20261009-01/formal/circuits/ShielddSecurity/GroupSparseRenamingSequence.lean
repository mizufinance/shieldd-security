import ShielddSecurity.GroupSparseRenamingCompletion

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupSparseRenamingSequence

variable {F : Type} [Field F]

/-- Every bounded patch reads the same functional completed source assignment.
The recursion sequences writes, not scalar multiplication or source graphs. -/
def run (base source : Nat → F) (columns : Nat → Nat) : List (List Nat) → Nat → F
  | [] => base
  | writes :: remaining => run (GroupSparseRenamingCompletion.extend base source columns writes) source columns remaining

theorem run_outside (base source : Nat → F) (columns : Nat → Nat)
    (blocks : List (List Nat)) (column : Nat)
    (outside : column ∉ blocks.flatten.map columns) :
    run base source columns blocks column = base column := by
  induction blocks generalizing base with
  | nil => rfl
  | cons writes remaining ih =>
      change column ∉ (writes ++ remaining.flatten).map columns at outside
      simp only [List.map_append,List.mem_append,not_or] at outside
      change run (GroupSparseRenamingCompletion.extend base source columns writes) source columns remaining column = base column
      rw [ih _ outside.2,GroupSparseRenamingCompletion.extend_preserves base source columns writes column outside.1]

theorem run_value (base source : Nat → F) (columns : Nat → Nat)
    (blocks : List (List Nat)) (column : Nat) (member : column ∈ blocks.flatten)
    (unique : ∀ left ∈ blocks.flatten, ∀ right ∈ blocks.flatten,
      columns left = columns right → left = right) :
    run base source columns blocks (columns column) = source column := by
  induction blocks generalizing base with
  | nil =>
      change column ∈ [] at member
      exact False.elim (List.not_mem_nil member)
  | cons writes remaining ih =>
      change column ∈ writes ++ remaining.flatten at member
      change ∀ left ∈ writes ++ remaining.flatten, ∀ right ∈ writes ++ remaining.flatten,
        columns left = columns right → left = right at unique
      have remainingUnique : ∀ left ∈ remaining.flatten, ∀ right ∈ remaining.flatten,
          columns left = columns right → left = right := by
        intro left leftMember right rightMember equality
        exact unique left (List.mem_append_right _ leftMember)
          right (List.mem_append_right _ rightMember) equality
      change run (GroupSparseRenamingCompletion.extend base source columns writes) source columns remaining
        (columns column) = source column
      by_cases later : column ∈ remaining.flatten
      · exact ih _ later remainingUnique
      · have headMember : column ∈ writes := (List.mem_append.mp member).resolve_right later
        have outside : columns column ∉ remaining.flatten.map columns := by
          intro mapped
          obtain ⟨other,otherMember,equality⟩ := List.mem_map.mp mapped
          have same : other = column := unique other (List.mem_append_right _ otherMember)
            column member equality
          exact later (same ▸ otherMember)
        rw [run_outside _ source columns remaining (columns column) outside]
        apply GroupSparseRenamingCompletion.extend_value base source columns writes column headMember
        intro left leftMember right rightMember equality
        exact unique left (List.mem_append_left _ leftMember)
          right (List.mem_append_left _ rightMember) equality

/-- Whole-write injectivity, rather than a separate injectivity assumption for
each patch, establishes the same result as one sparse extension. -/
theorem run_eq_extend (base source : Nat → F) (columns : Nat → Nat)
    (blocks : List (List Nat))
    (unique : ∀ left ∈ blocks.flatten, ∀ right ∈ blocks.flatten,
      columns left = columns right → left = right) :
    run base source columns blocks = GroupSparseRenamingCompletion.extend base source columns blocks.flatten := by
  funext column
  by_cases inside : column ∈ blocks.flatten.map columns
  · obtain ⟨original,member,equality⟩ := List.mem_map.mp inside
    subst column
    exact (run_value base source columns blocks original member unique).trans
      (GroupSparseRenamingCompletion.extend_value base source columns blocks.flatten original member unique).symm
  · exact (run_outside base source columns blocks column inside).trans
      (GroupSparseRenamingCompletion.extend_preserves base source columns blocks.flatten column inside).symm

/-- Actual source applications supply row truth from their owned constructor.
No target row truth is required, and nonwritten support exclusion covers the
whole sequence, including aliases across different bounded blocks. -/
theorem rows_complete {p : Nat} [CharP F p]
    (base source : Nat → F) (columns : Nat → Nat) (blocks : List (List Nat))
    (support : List Nat) (sourceRows actualRows : List Row)
    (unique : ∀ left ∈ blocks.flatten, ∀ right ∈ blocks.flatten,
      columns left = columns right → left = right)
    (noAlias : ∀ column ∈ support, column ∉ blocks.flatten →
      columns column ∉ blocks.flatten.map columns)
    (preserved : ∀ column ∈ support, column ∉ blocks.flatten →
      source column = base (columns column))
    (supports : ∀ row ∈ sourceRows, ∀ term ∈ row.a ++ row.b, term.1 ∈ support)
    (coverage : ∀ actual ∈ actualRows, ∃ original ∈ sourceRows,
      Compiler.canonical p (RowRenaming.linear columns original.a) = Compiler.canonical p actual.a ∧
      Compiler.canonical p (RowRenaming.linear columns original.b) = Compiler.canonical p actual.b)
    (completed : Satisfies source sourceRows) :
    Satisfies (run base source columns blocks) actualRows := by
  rw [run_eq_extend base source columns blocks unique]
  exact GroupSparseRenamingCompletion.rows_complete base source columns blocks.flatten support sourceRows actualRows
    unique noAlias preserved supports coverage completed

set_option pp.all true in
#check @run_outside
#print axioms run_outside
set_option pp.all true in
#check @run_value
#print axioms run_value
set_option pp.all true in
#check @run_eq_extend
#print axioms run_eq_extend
set_option pp.all true in
#check @rows_complete
#print axioms rows_complete

end ShielddSecurity.GroupSparseRenamingSequence
