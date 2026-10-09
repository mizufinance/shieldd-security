import ShielddSecurity.SourceGraphEvaluation
import ShielddSecurity.CompilerCertificateTransport

set_option maxHeartbeats 150000
set_option maxRecDepth 4096

namespace ShielddSecurity.CompilerGraphEvaluationSoundness
open Compiler

variable {F : Type} [Field F]

/-! Arbitrary satisfying row assignments determine the independent arithmetic
graph evaluation. Assertions are derived from certified rows, rather than
assumed of the evaluator. Actual graph/block identity, complete source assertion
coverage and graph-to-Transfer semantics remain separate instance obligations. -/

theorem compiled_values_eq_evaluation {p inputs nodes : Nat} [CharP F p]
    (graph : SourceGraph inputs nodes) (rows : List Row)
    (inputTerms : Nat → Linear) (expressions : Fin nodes → Expression)
    (certificates : ∀ index, NodeCertificate p rows inputTerms
      (graph.prior expressions index) (graph.node index) (expressions index))
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rows) :
    (fun index => expressionValue rho (expressions index)) =
      SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) := by
  apply Eq.symm
  apply SourceGraphEvaluation.computing_values_unique
  intro index
  exact node_certificate_sound rows inputTerms (graph.prior expressions index)
    (graph.node index) (expressions index) (certificates index) rho one four satisfied

theorem compiled_assertions_hold {p inputs nodes : Nat} [CharP F p]
    (graph : SourceGraph inputs nodes) (rows : List Row)
    (inputTerms : Nat → Linear) (expressions : Fin nodes → Expression)
    (nodeCertificates : ∀ index, NodeCertificate p rows inputTerms
      (graph.prior expressions index) (graph.node index) (expressions index))
    (assertionCertificates : ∀ assertion ∈ graph.assertions,
      AssertionCertificate p rows (expressions assertion.1) (expressions assertion.2))
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rows) :
    ∀ assertion ∈ graph.assertions,
      SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) assertion.1 =
        SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) assertion.2 := by
  have same := compiled_values_eq_evaluation graph rows inputTerms expressions
    nodeCertificates rho one four satisfied
  intro assertion member
  have asserted := assertion_certificate_sound rows _ _
    (assertionCertificates assertion member) rho satisfied
  exact (congrFun same assertion.1).symm.trans
    (asserted.trans (congrFun same assertion.2))

theorem certified_blocks_compute_and_assert {p inputs nodes : Nat} [CharP F p]
    (graph : SourceGraph inputs nodes) (fullRows : List Row)
    (nodeBlocks : Fin nodes → List Row)
    (assertionBlocks : (Fin nodes × Fin nodes) → List Row)
    (nodeCoverage : ∀ index,
      CompilerCertificateTransport.Coverage p (nodeBlocks index) fullRows)
    (assertionCoverage : ∀ assertion ∈ graph.assertions,
      CompilerCertificateTransport.Coverage p (assertionBlocks assertion) fullRows)
    (inputTerms : Nat → Linear) (expressions : Fin nodes → Expression)
    (nodeCertificates : ∀ index, NodeCertificate p (nodeBlocks index) inputTerms
      (graph.prior expressions index) (graph.node index) (expressions index))
    (assertionCertificates : ∀ assertion ∈ graph.assertions,
      AssertionCertificate p (assertionBlocks assertion)
        (expressions assertion.1) (expressions assertion.2))
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho fullRows) :
    (fun index => expressionValue rho (expressions index)) =
        SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) ∧
      ∀ assertion ∈ graph.assertions,
        SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) assertion.1 =
          SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) assertion.2 := by
  have nodesCovered := CompilerCertificateTransport.graph_nodes_covered
    graph nodeBlocks fullRows nodeCoverage inputTerms expressions nodeCertificates
  have assertionsCovered := CompilerCertificateTransport.graph_assertions_covered
    graph assertionBlocks fullRows assertionCoverage expressions assertionCertificates
  exact ⟨compiled_values_eq_evaluation graph fullRows inputTerms expressions
      nodesCovered rho one four satisfied,
    compiled_assertions_hold graph fullRows inputTerms expressions
      nodesCovered assertionsCovered rho one four satisfied⟩

set_option pp.all true in
#check @compiled_values_eq_evaluation
#print axioms compiled_values_eq_evaluation
set_option pp.all true in
#check @compiled_assertions_hold
#print axioms compiled_assertions_hold
set_option pp.all true in
#check @certified_blocks_compute_and_assert
#print axioms certified_blocks_compute_and_assert

end ShielddSecurity.CompilerGraphEvaluationSoundness
