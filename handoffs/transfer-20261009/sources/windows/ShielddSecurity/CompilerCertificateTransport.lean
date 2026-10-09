import ShielddSecurity.Compiler

set_option maxHeartbeats 150000
set_option maxRecDepth 4096

namespace ShielddSecurity.CompilerCertificateTransport
open Compiler

/-! Lift local compiler certificates through finite, canonical row-body
coverage. This permits symbolic block composition. An actual instance must
prove this coverage against complete original row data; hashes or observed
witness values cannot supply it. No row satisfaction is presumed here. -/
def Coverage (p : Nat) (localRows fullRows : List Row) : Prop :=
  ∀ localRow ∈ localRows, ∃ fullRow ∈ fullRows,
    canonical p localRow.a = canonical p fullRow.a ∧
    canonical p localRow.b = canonical p fullRow.b

theorem check_row_covered (p : Nat) (localRows fullRows : List Row)
    (coverage : Coverage p localRows fullRows) (expected : Row)
    (checked : checkRow p localRows expected = true) :
    checkRow p fullRows expected = true := by
  obtain ⟨localRow, member, accepted⟩ := List.any_eq_true.mp checked
  obtain ⟨fullRow, fullMember, left, right⟩ := coverage localRow member
  have equalities := of_decide_eq_true accepted
  apply List.any_eq_true.mpr
  refine ⟨fullRow, fullMember, ?_⟩
  apply decide_eq_true
  exact ⟨left.symm.trans equalities.1, right.symm.trans equalities.2⟩

theorem node_certificate_covered {p n : Nat} (localRows fullRows : List Row)
    (coverage : Coverage p localRows fullRows) (inputTerms : Nat → Linear)
    (earlier : Fin n → Expression) (node : SourceNode n) (output : Expression)
    (certificate : NodeCertificate p localRows inputTerms earlier node output) :
    NodeCertificate p fullRows inputTerms earlier node output := by
  cases certificate with
  | constant coefficient output equal => exact .constant coefficient output equal
  | input index output equal => exact .input index output equal
  | add left right x y output hx hy equal => exact .add left right x y output hx hy equal
  | foldedLeft left right x y output coefficient hx hy constant equal =>
      exact .foldedLeft left right x y output coefficient hx hy constant equal
  | foldedRight left right x y output coefficient hx hy constant equal =>
      exact .foldedRight left right x y output coefficient hx hy constant equal
  | deferred left right x y base hx hy ex ey =>
      exact .deferred left right x y base hx hy ex ey
  | square left right x y output hx hy equal row =>
      exact .square left right x y output hx hy equal
        (check_row_covered p localRows fullRows coverage _ row)
  | product left right x y output auxiliary hx hy minus plus =>
      exact .product left right x y output auxiliary hx hy
        (check_row_covered p localRows fullRows coverage _ minus)
        (check_row_covered p localRows fullRows coverage _ plus)

theorem assertion_certificate_covered {p : Nat} (localRows fullRows : List Row)
    (coverage : Coverage p localRows fullRows) (left right : Expression)
    (certificate : AssertionCertificate p localRows left right) :
    AssertionCertificate p fullRows left right := by
  cases certificate with
  | linear left right checked =>
      exact .linear left right (check_row_covered p localRows fullRows coverage _ checked)
  | squareLinear left right checked =>
      exact .squareLinear left right (check_row_covered p localRows fullRows coverage _ checked)
  | linearSquare left right checked =>
      exact .linearSquare left right (check_row_covered p localRows fullRows coverage _ checked)
  | squares left right auxiliary first second =>
      exact .squares left right auxiliary
        (check_row_covered p localRows fullRows coverage _ first)
        (check_row_covered p localRows fullRows coverage _ second)

theorem graph_nodes_covered {p inputs nodes : Nat} (graph : SourceGraph inputs nodes)
    (blocks : Fin nodes → List Row) (fullRows : List Row)
    (coverage : ∀ index, Coverage p (blocks index) fullRows)
    (inputTerms : Nat → Linear) (expressions : Fin nodes → Expression)
    (certificates : ∀ index, NodeCertificate p (blocks index) inputTerms
      (graph.prior expressions index) (graph.node index) (expressions index)) :
    ∀ index, NodeCertificate p fullRows inputTerms
      (graph.prior expressions index) (graph.node index) (expressions index) := by
  intro index
  exact node_certificate_covered (blocks index) fullRows (coverage index) inputTerms
    _ _ _ (certificates index)

theorem graph_assertions_covered {p inputs nodes : Nat} (graph : SourceGraph inputs nodes)
    (blocks : (Fin nodes × Fin nodes) → List Row) (fullRows : List Row)
    (coverage : ∀ assertion ∈ graph.assertions, Coverage p (blocks assertion) fullRows)
    (expressions : Fin nodes → Expression)
    (certificates : ∀ assertion ∈ graph.assertions,
      AssertionCertificate p (blocks assertion) (expressions assertion.1) (expressions assertion.2)) :
    ∀ assertion ∈ graph.assertions,
      AssertionCertificate p fullRows (expressions assertion.1) (expressions assertion.2) := by
  intro assertion member
  exact assertion_certificate_covered (blocks assertion) fullRows (coverage assertion member)
    _ _ (certificates assertion member)

set_option pp.all true in
#check @check_row_covered
#print axioms check_row_covered
set_option pp.all true in
#check @node_certificate_covered
#print axioms node_certificate_covered
set_option pp.all true in
#check @assertion_certificate_covered
#print axioms assertion_certificate_covered
set_option pp.all true in
#check @graph_nodes_covered
#print axioms graph_nodes_covered
set_option pp.all true in
#check @graph_assertions_covered
#print axioms graph_assertions_covered

end ShielddSecurity.CompilerCertificateTransport
