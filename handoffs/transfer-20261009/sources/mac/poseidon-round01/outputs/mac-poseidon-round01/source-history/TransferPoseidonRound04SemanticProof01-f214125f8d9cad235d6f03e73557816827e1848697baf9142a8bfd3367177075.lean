-- GENERATED instance of handwritten round-semantic-proof-template.lean.txt.
import ShielddSecurity.TransferPoseidonRound04SemanticChecks01
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferPoseidonRound04SemanticProof01
open Compiler CompilerIndexed01 Poseidon PoseidonIndexedRound01
open TransferPoseidonRound04 TransferPoseidonRound04SemanticData01
open TransferPoseidonRound04Proof01
open TransferPoseidonRound04SemanticChecks01

theorem column_cases (column : Fin 6) : column=0 ∨ column=1 ∨ column=2 ∨ column=3 ∨ column=4 ∨ column=5 := by
  have bound := column.isLt
  simp only [Fin.ext_iff]
  omega

theorem round_checked : checkRound p copy originalRows parameters 4 before shifted transformed after fifthHints=true := by
  simp only [checkRound,Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro column _
    rcases column_cases column with rfl | rfl | rfl | rfl | rfl | rfl
    · exact column0_checked
    · exact column1_checked
    · exact column2_checked
    · exact column3_checked
    · exact column4_checked
    · exact column5_checked
  · apply List.all_eq_true.mpr
    intro column _
    simp only [decide_eq_true_eq]
    rcases column_cases column with rfl | rfl | rfl | rfl | rfl | rfl
    · exact mix0_checked
    · exact mix1_checked
    · exact mix2_checked
    · exact mix3_checked
    · exact mix4_checked
    · exact mix5_checked

theorem production_checked : productionCheck originalRows parameters after fifthHints=true := by
  simp only [productionCheck,Bool.and_eq_true]
  exact ⟨⟨⟨actual_copy_checked,by decide +kernel⟩,by decide +kernel⟩,round_checked⟩

theorem before_binding (column : Fin 6) : before column=inputTerms column.val := by
  have checked := production_checked
  simp only [productionCheck,Bool.and_eq_true] at checked
  exact of_decide_eq_true (List.all_eq_true.mp checked.1.1.2 column (List.mem_finRange column))

theorem output_binding (column : Fin 6) : expressions (outputPorts column)=Expression.linear (after column) := by
  have checked := production_checked
  simp only [productionCheck,Bool.and_eq_true] at checked
  exact of_decide_eq_true (List.all_eq_true.mp checked.1.2 column (List.mem_finRange column))

theorem round_certificate : RoundCertificate p (unoutlineRows copy originalRows.toList)
    parameters 4 before shifted transformed after := by
  have checked := production_checked
  simp only [productionCheck,Bool.and_eq_true] at checked
  exact checkRound_sound p copy originalRows parameters 4 before shifted transformed after fifthHints checked.2

theorem ports_exact : graph.outputs=(List.finRange 6).map outputPorts := by decide +kernel

variable {F : Type} [Field F] [CharP F p]

theorem arbitrary_round_sound (rho : Nat → F) (one : rho 0=1) (four : (4:F)≠0)
    (satisfied : Satisfies rho originalRows.toList) :
    (fun column => expressionValue rho (expressions (outputPorts column))) =
      Poseidon.round (castParameters parameters) 4 (fun column => eval rho (inputTerms column.val)) := by
  have unoutlined := unoutline_rows_sound rho copy originalRows.toList satisfied
    (checkRowAt_sound p originalRows 4 _ actual_copy_checked)
  have result := round_certificate_sound rho (unoutlineRows copy originalRows.toList) parameters 4
    before shifted transformed after one four unoutlined round_certificate
  simpa only [output_binding,expressionValue,before_binding] using result

theorem arbitrary_graph_round (rho : Nat → F) (one : rho 0=1) (four : (4:F)≠0)
    (satisfied : Satisfies rho originalRows.toList) :
    (fun column => SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) (outputPorts column)) =
      Poseidon.round (castParameters parameters) 4 (fun column => eval rho (inputTerms column.val)) := by
  have values := arbitrary_assignment_sound rho one four satisfied
  have ports := congrArg (fun f => fun column => f (outputPorts column)) values
  exact ports.symm.trans (arbitrary_round_sound rho one four satisfied)

/-- Extends the prior assignment; cut inputs remain values of its original LCs.
The prior copy link is explicit and must be initialized or derived globally. -/
theorem completed_round (base : Nat → F) (one : base 0=1) (linked : base copy=base 0) (four : (4:F)≠0) :
    (fun column => expressionValue (completed base) (expressions (outputPorts column))) =
      Poseidon.round (castParameters parameters) 4 (fun column => eval base (inputTerms column.val)) := by
  have result := arbitrary_round_sound (completed base) ((completed_one base).trans one) four (completed_rows base linked)
  have ports := congrArg (fun f : Nat → F => fun column : Fin 6 => f column.val) (completed_cut_inputs base)
  exact result.trans (congrArg (Poseidon.round (castParameters parameters) 4) ports)

theorem total_native_round (base : Nat → F) (one : base 0=1) (linked : base copy=base 0) (four : (4:F)≠0) :
    Satisfies (completed base) originalRows.toList ∧
    (∀ column<22738,completed base column=base column) ∧
    completed base copy=base copy ∧
    (fun input => eval (completed base) (inputTerms input))=(fun input => eval base (inputTerms input)) ∧
    (fun column => expressionValue (completed base) (expressions (outputPorts column))) =
      Poseidon.round (castParameters parameters) 4 (fun column => eval base (inputTerms column.val)) :=
  ⟨completed_rows base linked,original_columns_preserved base,completed_copy base,
    completed_cut_inputs base,completed_round base one linked four⟩
end ShielddSecurity.TransferPoseidonRound04SemanticProof01

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticProof01.column_cases
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticProof01.column_cases

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticProof01.round_checked
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticProof01.round_checked

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticProof01.production_checked
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticProof01.production_checked

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticProof01.before_binding
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticProof01.before_binding

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticProof01.output_binding
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticProof01.output_binding

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticProof01.round_certificate
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticProof01.round_certificate

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticProof01.ports_exact
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticProof01.ports_exact

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticProof01.arbitrary_round_sound
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticProof01.arbitrary_round_sound

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticProof01.arbitrary_graph_round
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticProof01.arbitrary_graph_round

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticProof01.completed_round
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticProof01.completed_round

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04SemanticProof01.total_native_round
#print axioms ShielddSecurity.TransferPoseidonRound04SemanticProof01.total_native_round
