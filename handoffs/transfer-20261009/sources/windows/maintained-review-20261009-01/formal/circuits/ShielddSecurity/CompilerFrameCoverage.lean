import ShielddSecurity.GroupFixedCircuitBounds

set_option maxHeartbeats 100000

namespace ShielddSecurity.CompilerFrameCoverage

open GroupFixedCircuitBounds

/-- A dependency's independently checked support certificate travels with its
actual row list. Assembling blocks does not rewalk their sparse expressions. -/
structure CoveredBlock (origin copy : Nat) (frame : Frame) where
  rows : List Row
  covered : RowsCovered origin copy frame rows

/-- Bounded original rows only. This checker does not inspect values or assert
row truth: it certifies which columns later construction must preserve. -/
def checkRows (origin copy : Nat) (frame : Frame) (rows : List Row) : Bool :=
  rows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (covers origin copy frame term.1)))

theorem checked_rows (origin copy : Nat) (frame : Frame) (rows : List Row)
    (checked : checkRows origin copy frame rows = true) :
    RowsCovered origin copy frame rows := by
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp checked row member) term present)

theorem append_rows (origin copy : Nat) (frame : Frame) (left right : List Row)
    (leftCovered : RowsCovered origin copy frame left)
    (rightCovered : RowsCovered origin copy frame right) :
    RowsCovered origin copy frame (left ++ right) := by
  intro row member term present
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact leftCovered row leftMember term present
  · exact rightCovered row rightMember term present

theorem flat_map_rows {I : Type} (origin copy : Nat) (frame : Frame)
    (parts : List I) (rows : I → List Row)
    (covered : ∀ part ∈ parts, RowsCovered origin copy frame (rows part)) :
    RowsCovered origin copy frame (parts.flatMap rows) := by
  intro row member term present
  obtain ⟨part,partMember,rowMember⟩ := List.mem_flatMap.mp member
  exact covered part partMember row rowMember term present

theorem grouped_flat_map {I R : Type} (parts : List (List I)) (rows : I → List R) :
    (parts.foldr List.append []).flatMap rows = parts.flatMap (fun part => part.flatMap rows) := by
  induction parts with
  | nil => rfl
  | cons part rest ih =>
      change (part ++ rest.foldr List.append []).flatMap rows =
        part.flatMap rows ++ rest.flatMap (fun block => block.flatMap rows)
      rw [List.flatMap_append,ih]

/-- An exact earlier product origin broadens the protected compiler interval.
Previously proved scoped fixed-window coverage can be reused symbolically. -/
theorem lower_origin_rows (earlier later copy : Nat) (frame : Frame) (rows : List Row)
    (order : earlier ≤ later) (covered : RowsCovered later copy frame rows) :
    RowsCovered earlier copy frame rows := by
  intro row member term present
  rcases covered row member term present with low | high | copied
  · exact Or.inl low
  · exact Or.inr (Or.inl ⟨Nat.le_trans order high.1,high.2⟩)
  · exact Or.inr (Or.inr copied)

set_option pp.all true in
#check @checked_rows
#print axioms checked_rows
set_option pp.all true in
#check @append_rows
#print axioms append_rows
set_option pp.all true in
#check @flat_map_rows
#print axioms flat_map_rows
set_option pp.all true in
#check @grouped_flat_map
#print axioms grouped_flat_map
set_option pp.all true in
#check @lower_origin_rows
#print axioms lower_origin_rows

end ShielddSecurity.CompilerFrameCoverage
