import ShielddSecurity.CompilerFrameCoverage

set_option maxHeartbeats 100000

namespace ShielddSecurity.CompilerWriteExclusion

/-- Sparse exclusion includes owned source patches, independently of the
allocation frame used for later circuit stages. -/
def RowsOutside (writes : List Nat) (rows : List Row) : Prop :=
  ∀ row ∈ rows, ∀ term ∈ row.a ++ row.b, term.1 ∉ writes

def checkRows (writes : List Nat) (rows : List Row) : Bool :=
  rows.all (fun row => (row.a ++ row.b).all (fun term => decide (term.1 ∉ writes)))

theorem checked_rows (writes : List Nat) (rows : List Row)
    (checked : checkRows writes rows = true) : RowsOutside writes rows := by
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp checked row member) term present)

theorem append_rows (writes : List Nat) (left right : List Row)
    (leftOutside : RowsOutside writes left) (rightOutside : RowsOutside writes right) :
    RowsOutside writes (left ++ right) := by
  intro row member term present
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact leftOutside row leftMember term present
  · exact rightOutside row rightMember term present

theorem flat_map_rows {I : Type} (writes : List Nat) (parts : List I) (rows : I → List Row)
    (outside : ∀ part ∈ parts, RowsOutside writes (rows part)) :
    RowsOutside writes (parts.flatMap rows) := by
  intro row member term present
  obtain ⟨part,partMember,rowMember⟩ := List.mem_flatMap.mp member
  exact outside part partMember row rowMember term present

set_option pp.all true in
#check @checked_rows
#print axioms checked_rows
set_option pp.all true in
#check @append_rows
#print axioms append_rows
set_option pp.all true in
#check @flat_map_rows
#print axioms flat_map_rows

end ShielddSecurity.CompilerWriteExclusion
