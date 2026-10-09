import ShielddSecurity.RowRenaming
import ShielddSecurity.GroupCircuitOrder

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupSparseRenamingCompletion

variable {F : Type} [Field F]

/-- Read a completed source value through a finite owned-write list. The
column map need not be injective on unrelated source or target columns. -/
def values (source : Nat → F) (columns : Nat → Nat) : List Nat → Nat → F
  | [], _ => 0
  | owned :: tail, target =>
      if columns owned = target then source owned else values source columns tail target

/-- Construct only the mapped owned columns. All other target values remain
from the caller's assignment, independently of their current contents. -/
def extend (base source : Nat → F) (columns : Nat → Nat) (writes : List Nat) : Nat → F :=
  patchAssignment base (values source columns writes) (writes.map columns)

theorem mapped_value (source : Nat → F) (columns : Nat → Nat) (writes : List Nat)
    (column : Nat) (member : column ∈ writes)
    (unique : ∀ left ∈ writes, ∀ right ∈ writes,
      columns left = columns right → left = right) :
    values source columns writes (columns column) = source column := by
  induction writes generalizing column with
  | nil => simp only [List.not_mem_nil] at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | present
      · subst column
        rw [values,if_pos rfl]
      · by_cases sameImage : columns head = columns column
        · have same := unique head (by simp) column (List.mem_cons_of_mem _ present) sameImage
          rw [values,if_pos sameImage,same]
        · rw [values,if_neg sameImage]
          exact ih column present (by
            intro left leftMember right rightMember equality
            exact unique left (List.mem_cons_of_mem _ leftMember)
              right (List.mem_cons_of_mem _ rightMember) equality)

theorem extend_value (base source : Nat → F) (columns : Nat → Nat) (writes : List Nat)
    (column : Nat) (member : column ∈ writes)
    (unique : ∀ left ∈ writes, ∀ right ∈ writes,
      columns left = columns right → left = right) :
    extend base source columns writes (columns column) = source column := by
  have mapped : columns column ∈ writes.map columns := List.mem_map.mpr ⟨column,member,rfl⟩
  simp only [extend,patchAssignment,if_pos mapped]
  exact mapped_value source columns writes column member unique

theorem extend_preserves (base source : Nat → F) (columns : Nat → Nat) (writes : List Nat)
    (column : Nat) (outside : column ∉ writes.map columns) :
    extend base source columns writes column = base column :=
  patchAssignment_preserves base _ _ column outside

/-- Only the finite source supports used by actual rows or point/bit operands
must agree. Non-owned source supports must avoid mapped writes. An actual
application derives source preservation from the owned constructor's write
exclusion theorem; it does not posit a desired source/output meaning. -/
theorem pullback_agrees (base source : Nat → F) (columns : Nat → Nat)
    (writes support : List Nat)
    (unique : ∀ left ∈ writes, ∀ right ∈ writes,
      columns left = columns right → left = right)
    (noAlias : ∀ column ∈ support, column ∉ writes → columns column ∉ writes.map columns)
    (preserved : ∀ column ∈ support, column ∉ writes → source column = base (columns column)) :
    ∀ column ∈ support, extend base source columns writes (columns column) = source column := by
  intro column member
  by_cases written : column ∈ writes
  · exact extend_value base source columns writes column written unique
  · have outside : columns column ∉ writes.map columns := noAlias column member written
    rw [extend_preserves base source columns writes (columns column) outside]
    exact (preserved column member written).symm

/-- Complete every retained target row from the proved completed source rows
and exact canonical side coverage. These are local transport hypotheses: the
whole RNK application must supply source row truth from its owned constructor,
finite support/write checks, and the accepted actual ordinary-row selection. -/
theorem rows_complete {p : Nat} [CharP F p]
    (base source : Nat → F) (columns : Nat → Nat) (writes support : List Nat)
    (sourceRows actualRows : List Row)
    (unique : ∀ left ∈ writes, ∀ right ∈ writes,
      columns left = columns right → left = right)
    (noAlias : ∀ column ∈ support, column ∉ writes → columns column ∉ writes.map columns)
    (preserved : ∀ column ∈ support, column ∉ writes → source column = base (columns column))
    (supports : ∀ row ∈ sourceRows, ∀ term ∈ row.a ++ row.b, term.1 ∈ support)
    (coverage : ∀ actual ∈ actualRows, ∃ original ∈ sourceRows,
      Compiler.canonical p (RowRenaming.linear columns original.a) = Compiler.canonical p actual.a ∧
      Compiler.canonical p (RowRenaming.linear columns original.b) = Compiler.canonical p actual.b)
    (completed : Satisfies source sourceRows) :
    Satisfies (extend base source columns writes) actualRows := by
  let built := extend base source columns writes
  have agrees := pullback_agrees base source columns writes support unique noAlias preserved
  intro actual member
  obtain ⟨original,originalMember,checkedA,checkedB⟩ := coverage actual member
  have evalSide (terms : Linear) (inside : ∀ term ∈ terms, term.1 ∈ support) :
      eval built (RowRenaming.linear columns terms) = eval source terms := by
    rw [RowRenaming.eval_linear]
    apply eval_agrees
    intro term present
    exact agrees term.1 (inside term present)
  have a := Compiler.canonical_equal built (RowRenaming.linear columns original.a) actual.a checkedA
  have b := Compiler.canonical_equal built (RowRenaming.linear columns original.b) actual.b checkedB
  change Square (eval built actual.a) (eval built actual.b)
  rw [← a,← b,
    evalSide original.a (by intro term present; exact supports original originalMember term (List.mem_append_left _ present)),
    evalSide original.b (by intro term present; exact supports original originalMember term (List.mem_append_right _ present))]
  exact completed original originalMember

set_option pp.all true in
#check @mapped_value
#print axioms mapped_value
set_option pp.all true in
#check @extend_value
#print axioms extend_value
set_option pp.all true in
#check @extend_preserves
#print axioms extend_preserves
set_option pp.all true in
#check @pullback_agrees
#print axioms pullback_agrees
set_option pp.all true in
#check @rows_complete
#print axioms rows_complete

end ShielddSecurity.GroupSparseRenamingCompletion
