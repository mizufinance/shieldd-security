-- GENERATED instance of handwritten absorption-semantic-proof-template.lean.txt.
import ShielddSecurity.TransferPoseidonAbsorb02SemanticChecks01
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01
open Compiler CompilerIndexed01 Poseidon PoseidonIndexedFolded02
open TransferPoseidonAbsorb02 TransferPoseidonAbsorb02SemanticData01
open TransferPoseidonAbsorb02Proof01
open TransferPoseidonAbsorb02SemanticChecks01

theorem column_cases (column : Fin 6) : column=0 ∨ column=1 ∨ column=2 ∨ column=3 ∨ column=4 ∨ column=5 := by
  have bound := column.isLt
  simp only [Fin.ext_iff]
  omega

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.column_cases
#print axioms ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.column_cases

theorem round_checked : checkRound p copy originalRows parameters 0 before shifted transformed after fifthHints=true := by
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

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.round_checked
#print axioms ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.round_checked

theorem production_checked : productionCheck originalRows parameters after fifthHints 23 4 orderedInputs=true := by
  simp only [productionCheck,Bool.and_eq_true]
  exact ⟨⟨⟨actual_copy_checked,absorption_checked⟩,ports_checked⟩,round_checked⟩

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.production_checked
#print axioms ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.production_checked

theorem absorption_binding (column : Fin 6) : canonical p (before column)=
    canonical p (absorbLinear (initialLinear 23 4) (orderedInputs.map inputTerms) column) := by
  have checked := production_checked
  simp only [productionCheck,Bool.and_eq_true,absorptionCheck] at checked
  exact of_decide_eq_true (List.all_eq_true.mp checked.1.1.2 column (List.mem_finRange column))

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.absorption_binding
#print axioms ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.absorption_binding

theorem ordered_inputs_exact : orderedInputs=[11,12,18,19] := rfl

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.ordered_inputs_exact
#print axioms ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.ordered_inputs_exact

theorem iv_exact : 4*256+23=1047 := by decide

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.iv_exact
#print axioms ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.iv_exact

theorem output_binding (column : Fin 6) : expressions (outputPorts column)=Expression.linear (after column) := by
  have checked := production_checked
  simp only [productionCheck,Bool.and_eq_true] at checked
  exact of_decide_eq_true (List.all_eq_true.mp checked.1.2 column (List.mem_finRange column))

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.output_binding
#print axioms ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.output_binding

theorem round_certificate : RoundCertificate p (unoutlineRows copy originalRows.toList)
    parameters 0 before shifted transformed after := by
  have checked := production_checked
  simp only [productionCheck,Bool.and_eq_true] at checked
  exact checkRound_sound p copy originalRows parameters 0 before shifted transformed after fifthHints checked.2

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.round_certificate
#print axioms ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.round_certificate

theorem ports_exact : graph.outputs=(List.finRange 6).map outputPorts := by decide +kernel

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.ports_exact
#print axioms ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.ports_exact

variable {F : Type} [Field F] [CharP F p]

theorem before_values (rho : Nat → F) (one : rho 0=1) :
    (fun column => eval rho (before column)) =
      Poseidon.absorb (Poseidon.initial 23 4) (orderedInputs.map (fun input => eval rho (inputTerms input))) := by
  have same : (fun column => eval rho (before column)) =
      (fun column => eval rho (absorbLinear (initialLinear 23 4) (orderedInputs.map inputTerms) column)) := by
    funext column
    exact Compiler.canonical_equal rho _ _ (absorption_binding column)
  have absorb := eval_absorbLinear rho (initialLinear (width:=6) 23 4) (orderedInputs.map inputTerms)
  rw [eval_initialLinear rho one 23 4] at absorb
  exact same.trans (by simpa only [List.map_map,Function.comp_def] using absorb)

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.before_values
#print axioms ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.before_values

theorem arbitrary_round_sound (rho : Nat → F) (one : rho 0=1) (four : (4:F)≠0)
    (satisfied : Satisfies rho originalRows.toList) :
    (fun column => expressionValue rho (expressions (outputPorts column))) =
      Poseidon.round (castParameters parameters) 0 (Poseidon.absorb (Poseidon.initial 23 4) (orderedInputs.map (fun input => eval rho (inputTerms input)))) := by
  have unoutlined := unoutline_rows_sound rho copy originalRows.toList satisfied
    (checkRowAt_sound p originalRows 16 _ actual_copy_checked)
  have result := round_certificate_sound rho (unoutlineRows copy originalRows.toList) parameters 0
    before shifted transformed after one four unoutlined round_certificate
  rw [before_values rho one] at result
  simpa only [output_binding,expressionValue] using result

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.arbitrary_round_sound
#print axioms ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.arbitrary_round_sound

theorem arbitrary_graph_round (rho : Nat → F) (one : rho 0=1) (four : (4:F)≠0)
    (satisfied : Satisfies rho originalRows.toList) :
    (fun column => SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) (outputPorts column)) =
      Poseidon.round (castParameters parameters) 0 (Poseidon.absorb (Poseidon.initial 23 4) (orderedInputs.map (fun input => eval rho (inputTerms input)))) := by
  have values := arbitrary_assignment_sound rho one four satisfied
  have ports := congrArg (fun f => fun column => f (outputPorts column)) values
  exact ports.symm.trans (arbitrary_round_sound rho one four satisfied)

/- Extends the prior assignment; the four original witness inputs retain their LC values.
The prior copy link is explicit and must be initialized or derived globally. -/
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.arbitrary_graph_round
#print axioms ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.arbitrary_graph_round

theorem completed_round (base : Nat → F) (one : base 0=1) (linked : base copy=base 0) (four : (4:F)≠0) :
    (fun column => expressionValue (completed base) (expressions (outputPorts column))) =
      Poseidon.round (castParameters parameters) 0 (Poseidon.absorb (Poseidon.initial 23 4) (orderedInputs.map (fun input => eval base (inputTerms input)))) := by
  have result := arbitrary_round_sound (completed base) ((completed_one base).trans one) four (completed_rows base linked)
  have ports := congrArg (fun f : Nat → F => orderedInputs.map f) (completed_source_inputs base)
  exact result.trans (congrArg (fun inputs => Poseidon.round (castParameters parameters) 0 (Poseidon.absorb (Poseidon.initial 23 4) inputs)) ports)

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.completed_round
#print axioms ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.completed_round

theorem total_native_round (base : Nat → F) (one : base 0=1) (linked : base copy=base 0) (four : (4:F)≠0) :
    Satisfies (completed base) originalRows.toList ∧
    (∀ column<22738,completed base column=base column) ∧
    completed base copy=base copy ∧
    (fun input => eval (completed base) (inputTerms input))=(fun input => eval base (inputTerms input)) ∧
    (fun column => expressionValue (completed base) (expressions (outputPorts column))) =
      Poseidon.round (castParameters parameters) 0 (Poseidon.absorb (Poseidon.initial 23 4) (orderedInputs.map (fun input => eval base (inputTerms input)))) :=
  ⟨completed_rows base linked,original_columns_preserved base,completed_copy base,
    completed_source_inputs base,completed_round base one linked four⟩
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.total_native_round
#print axioms ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01.total_native_round

end ShielddSecurity.TransferPoseidonAbsorb02SemanticProof01
