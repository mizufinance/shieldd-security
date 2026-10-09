import ShielddSecurity.TransferFirstSubgroupLeaf01
import ShielddSecurity.TransferFirstSubgroupLeaf02
import ShielddSecurity.CompilerGraphEvaluationSoundness

set_option maxHeartbeats 800000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferFirstSubgroupCertificates01
open Compiler CompilerCompletion CompilerIndexed01 TransferFirstSubgroupData01

def unoutlinedArithmetic : Array Row := arithmeticRows.map (fun row => ⟨unoutline copy row.a,unoutline copy row.b⟩)
def unoutlinedOriginal : Array Row := originalRows.map (fun row => ⟨unoutline copy row.a,unoutline copy row.b⟩)

theorem all_index_coverage (index : Fin 80) :
    index ∈ TransferFirstSubgroupLeaf01.indices ∨ index ∈ TransferFirstSubgroupLeaf02.indices := by
  by_cases first : index.val < 54
  · left
    apply List.mem_map.mpr
    refine ⟨⟨index.val,first⟩,List.mem_finRange _,?_⟩
    apply Fin.ext
    simp
  · right
    apply List.mem_map.mpr
    refine ⟨⟨index.val-54,by omega⟩,List.mem_finRange _,?_⟩
    apply Fin.ext
    simp
    omega

theorem node_certificates (index : Fin 80) :
    NodeCertificate p (unoutlineRows copy arithmeticRows.toList) inputTerms
      (graph.prior expressions index) (graph.node index) (expressions index) := by
  rcases all_index_coverage index with first | second
  · exact TransferFirstSubgroupLeaf01.certificates index first
  · exact TransferFirstSubgroupLeaf02.certificates index second

theorem assertions_checked : checkAssertions p copy originalRows graph expressions assertionHints = true := by
  decide +kernel

theorem assertion_certificates (assertion : Fin 80 × Fin 80) (member : assertion ∈ graph.assertions) :
    AssertionCertificate p (unoutlineRows copy originalRows.toList)
      (expressions assertion.1) (expressions assertion.2) :=
  checkAssertions_sound p copy originalRows graph expressions assertionHints assertions_checked assertion member

theorem arithmetic_coverage_checked :
    checkOriginalCoverage p copy arithmeticRows emittedArithmetic arithmeticMapping = true := by decide +kernel

theorem original_coverage_checked :
    checkOriginalCoverage p copy originalRows emittedOriginal originalMapping = true := by decide +kernel

theorem arithmetic_emitted_identity : emittedArithmetic.toList = emitted arithmeticSteps := by
  simp [emittedArithmetic]

theorem original_emitted_identity : emittedOriginal.toList = emitted allSteps := by
  simp [emittedOriginal]

theorem arithmetic_reverse_coverage : ∀ actual ∈ arithmeticRows.toList,
    ∃ expected ∈ emitted arithmeticSteps,
      canonical p (unoutline copy actual.a) = canonical p expected.a ∧
      canonical p (unoutline copy actual.b) = canonical p expected.b := by
  simpa only [arithmetic_emitted_identity] using
    checkOriginalCoverage_sound p copy arithmeticRows emittedArithmetic arithmeticMapping arithmetic_coverage_checked

theorem original_reverse_coverage : ∀ actual ∈ originalRows.toList,
    ∃ expected ∈ emitted allSteps,
      canonical p (unoutline copy actual.a) = canonical p expected.a ∧
      canonical p (unoutline copy actual.b) = canonical p expected.b := by
  simpa only [original_emitted_identity] using
    checkOriginalCoverage_sound p copy originalRows emittedOriginal originalMapping original_coverage_checked

theorem inclusion_checked :
    checkOriginalCoverage p 0 unoutlinedArithmetic unoutlinedOriginal nodeInclusionMapping = true := by decide +kernel

theorem node_coverage : CompilerCertificateTransport.Coverage p
    (unoutlineRows copy arithmeticRows.toList) (unoutlineRows copy originalRows.toList) := by
  have result := checked_inclusion p unoutlinedArithmetic unoutlinedOriginal nodeInclusionMapping inclusion_checked
  simpa [unoutlinedArithmetic,unoutlinedOriginal,unoutlineRows] using result

theorem original_node_certificates (index : Fin 80) :
    NodeCertificate p (unoutlineRows copy originalRows.toList) inputTerms
      (graph.prior expressions index) (graph.node index) (expressions index) :=
  CompilerCertificateTransport.node_certificate_covered _ _ node_coverage inputTerms
    (graph.prior expressions index) (graph.node index) (expressions index) (node_certificates index)

theorem actual_copy_checked :
    checkRowAt p originalRows 70 ⟨[(0,1),(copy,-1)],[]⟩ = true := by decide +kernel

theorem arithmetic_copy_checked :
    checkRowAt p arithmeticRows 64 ⟨[(0,1),(copy,-1)],[]⟩ = true := by decide +kernel

variable {F : Type} [Field F] [CharP F p]

theorem actual_copy_link (rho : Nat → F) (satisfied : Satisfies rho originalRows.toList) : rho copy = rho 0 := by
  have equal := checked_assertion_sound rho originalRows.toList [(0,1)] [(copy,1)] satisfied
    (by simpa [subtract,scaleLinear] using checkRowAt_sound p originalRows 70 _ actual_copy_checked)
  simpa [eval] using equal.symm

theorem arbitrary_assignment_sound (rho : Nat → F) (one : rho 0=1) (four : (4:F)≠0)
    (satisfied : Satisfies rho originalRows.toList) :
    (fun i => expressionValue rho (expressions i)) =
      SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) ∧
    ∀ assertion ∈ graph.assertions,
      SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) assertion.1 =
      SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) assertion.2 := by
  have unoutlined := unoutline_rows_sound rho copy originalRows.toList satisfied
    (checkRowAt_sound p originalRows 70 _ actual_copy_checked)
  exact ⟨CompilerGraphEvaluationSoundness.compiled_values_eq_evaluation graph _ inputTerms expressions
      original_node_certificates rho one four unoutlined,
    CompilerGraphEvaluationSoundness.compiled_assertions_hold graph _ inputTerms expressions
      original_node_certificates assertion_certificates rho one four unoutlined⟩

end ShielddSecurity.TransferFirstSubgroupCertificates01

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.all_index_coverage
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.all_index_coverage

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.node_certificates
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.node_certificates

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.assertions_checked
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.assertions_checked

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.assertion_certificates
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.assertion_certificates

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.arithmetic_coverage_checked
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.arithmetic_coverage_checked

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.original_coverage_checked
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.original_coverage_checked

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.arithmetic_emitted_identity
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.arithmetic_emitted_identity

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.original_emitted_identity
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.original_emitted_identity

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.arithmetic_reverse_coverage
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.arithmetic_reverse_coverage

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.original_reverse_coverage
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.original_reverse_coverage

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.inclusion_checked
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.inclusion_checked

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.node_coverage
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.node_coverage

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.original_node_certificates
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.original_node_certificates

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.actual_copy_checked
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.actual_copy_checked

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.arithmetic_copy_checked
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.arithmetic_copy_checked

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.actual_copy_link
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.actual_copy_link

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCertificates01.arbitrary_assignment_sound
#print axioms ShielddSecurity.TransferFirstSubgroupCertificates01.arbitrary_assignment_sound
