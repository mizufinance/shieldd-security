import ShielddSecurity.FiniteColumnRenaming

set_option maxHeartbeats 200000

namespace ShielddSecurity.FiniteWritePatch

def assignment {F : Type} (tree : FiniteColumnRenaming.Tree)
    (base built : Nat → F) (column : Nat) : F :=
  if (FiniteColumnRenaming.lookup tree column).isSome then built column else base column

theorem at_selected {F : Type} (tree : FiniteColumnRenaming.Tree) (base built : Nat → F)
    (column : Nat) (selected : (FiniteColumnRenaming.lookup tree column).isSome = true) :
    assignment tree base built column = built column := by
  simp [assignment,selected]

theorem preserves {F : Type} (tree : FiniteColumnRenaming.Tree) (base built : Nat → F)
    (column : Nat) (outside : FiniteColumnRenaming.lookup tree column = none) :
    assignment tree base built column = base column := by
  simp [assignment,outside]

theorem preserves_rows {F : Type} [Field F]
    (tree : FiniteColumnRenaming.Tree) (base built : Nat → F) (rows : List Row)
    (outside : ∀ row ∈ rows,∀ term ∈ row.a ++ row.b,
      FiniteColumnRenaming.lookup tree term.1 = none)
    (satisfied : Satisfies base rows) : Satisfies (assignment tree base built) rows := by
  intro row member
  have agree (terms : Linear) (included : ∀ term ∈ terms,term ∈ row.a ++ row.b) :
      eval (assignment tree base built) terms = eval base terms := by
    apply eval_agrees
    intro term present
    exact preserves tree base built term.1 (outside row member term (included term present))
  rw [agree row.a (by intro term present;exact List.mem_append_left _ present),
    agree row.b (by intro term present;exact List.mem_append_right _ present)]
  exact satisfied row member

theorem built_rows {F : Type} [Field F]
    (tree : FiniteColumnRenaming.Tree) (base built : Nat → F) (rows : List Row)
    (support : ∀ row ∈ rows,∀ term ∈ row.a ++ row.b,
      (FiniteColumnRenaming.lookup tree term.1).isSome = true ∨ base term.1 = built term.1)
    (satisfied : Satisfies built rows) : Satisfies (assignment tree base built) rows := by
  intro row member
  have agree (terms : Linear) (included : ∀ term ∈ terms,term ∈ row.a ++ row.b) :
      eval (assignment tree base built) terms = eval built terms := by
    apply eval_agrees
    intro term present
    rcases support row member term (included term present) with selected | same
    · exact at_selected tree base built term.1 selected
    · unfold assignment
      split
      · rfl
      · exact same
  rw [agree row.a (by intro term present;exact List.mem_append_left _ present),
    agree row.b (by intro term present;exact List.mem_append_right _ present)]
  exact satisfied row member

set_option pp.all true in
#check @at_selected
#print axioms at_selected
set_option pp.all true in
#check @preserves
#print axioms preserves
set_option pp.all true in
#check @preserves_rows
#print axioms preserves_rows
set_option pp.all true in
#check @built_rows
#print axioms built_rows

end ShielddSecurity.FiniteWritePatch
