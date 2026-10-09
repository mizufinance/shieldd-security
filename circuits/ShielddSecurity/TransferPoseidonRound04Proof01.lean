-- GENERATED instance wrapper from round-proof-template.lean.txt; edit template.
import ShielddSecurity.TransferPoseidonRound04Leaf01
import ShielddSecurity.TransferPoseidonRound04Leaf02
import ShielddSecurity.TransferPoseidonRound04Program01
import ShielddSecurity.CompilerIndexCoverage01
import ShielddSecurity.CompilerPriorFrame01
import ShielddSecurity.CompilerOrder
import ShielddSecurity.CompilerGraphEvaluationSoundness
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferPoseidonRound04Proof01
open Compiler CompilerCompletion CompilerIndexed01
open TransferPoseidonRound04 TransferPoseidonRound04Program01

theorem coverage_checked : CompilerIndexCoverage01.checkCoverage
    (TransferPoseidonRound04Leaf01.indices++TransferPoseidonRound04Leaf02.indices)=true := by decide +kernel

theorem all_index_coverage (index : Fin 135) :
    index∈TransferPoseidonRound04Leaf01.indices ∨ index∈TransferPoseidonRound04Leaf02.indices :=
  List.mem_append.mp (CompilerIndexCoverage01.checkCoverage_sound _ coverage_checked index)

theorem node_certificates (index : Fin 135) :
    NodeCertificate p (unoutlineRows copy originalRows.toList) inputTerms
      (graph.prior expressions index) (graph.node index) (expressions index) := by
  rcases all_index_coverage index with first | second
  · exact TransferPoseidonRound04Leaf01.certificates index first
  · exact TransferPoseidonRound04Leaf02.certificates index second

theorem actual_copy_checked :
    checkRowAt p originalRows 4 ⟨[(0,1),(copy,-1)],[]⟩=true := by decide +kernel

theorem rows_coverage_checked :
    checkOriginalCoverage p copy originalRows emittedRows rowMapping=true := by decide +kernel

theorem emitted_identity : emittedRows.toList=emitted steps := by simp [emittedRows]

theorem reverse_coverage : ∀ actual∈originalRows.toList,∃ expected∈emitted steps,
    canonical p (unoutline copy actual.a)=canonical p expected.a ∧
      canonical p (unoutline copy actual.b)=canonical p expected.b := by
  simpa only [emitted_identity] using
    checkOriginalCoverage_sound p copy originalRows emittedRows rowMapping rows_coverage_checked

theorem ordered_check : CompilerOrder.checkOrder [0,copy] [] steps=true := by decide +kernel

theorem ordered : Topological [0,copy] [] steps := CompilerOrder.checked_order _ _ _ ordered_check

theorem writes_check : (PoseidonCompletion.writes steps).all (fun column => decide (22738≤column))=true := by decide +kernel

theorem writes_lower_bound (column : Nat) (member : column∈PoseidonCompletion.writes steps) : 22738≤column :=
  of_decide_eq_true (List.all_eq_true.mp writes_check column member)

theorem cut_support_checked : CompilerPriorFrame01.checkSupport 6 inputTerms steps=true := by decide +kernel

theorem input_terms_outside (input : Nat) (bound : 6≤input) : inputTerms input=[] := by
  have same : input=(input-6)+6 := by omega
  rw [same]
  rfl

variable {F : Type} [Field F] [CharP F p]

theorem actual_copy_link (rho : Nat → F) (satisfied : Satisfies rho originalRows.toList) : rho copy=rho 0 := by
  have equal := checked_assertion_sound rho originalRows.toList [(0,1)] [(copy,1)] satisfied
    (by simpa [subtract,scaleLinear] using checkRowAt_sound p originalRows 4 _ actual_copy_checked)
  simpa [eval] using equal.symm

theorem arbitrary_assignment_sound (rho : Nat → F) (one : rho 0=1) (four : (4:F)≠0)
    (satisfied : Satisfies rho originalRows.toList) :
    (fun index => expressionValue rho (expressions index)) =
      SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) := by
  have unoutlined := unoutline_rows_sound rho copy originalRows.toList satisfied
    (checkRowAt_sound p originalRows 4 _ actual_copy_checked)
  exact CompilerGraphEvaluationSoundness.compiled_values_eq_evaluation graph _ inputTerms expressions
    node_certificates rho one four unoutlined

def completed (base : Nat → F) : Nat → F := run base steps

theorem legal (base : Nat → F) : Legal base steps := by
  simp [steps,materializedSteps,copyStep,Legal,Step.Legal]

/-- Local construction extends a prior assignment; six cut states are its LC
values, not six new unconstrained witness columns. -/
theorem completed_rows (base : Nat → F) (linked : base copy=base 0) :
    Satisfies (completed base) originalRows.toList :=
  (original_rows_complete base steps [0,copy] originalRows.toList copy ordered (legal _)
    (by simp) (by simp) linked reverse_coverage).1

theorem original_columns_preserved (base : Nat → F) (column : Nat) (bound : column<22738) :
    completed base column=base column := by
  apply PoseidonCompletion.run_outside
  intro member
  have lower:=writes_lower_bound column member
  omega

theorem original_inputs_preserved (base : Nat → F) (input : Nat) (bound : input<22735) :
    completed base (3+input)=base (3+input) := original_columns_preserved base _ (by omega)

theorem completed_one (base : Nat → F) : completed base 0=base 0 :=
  original_columns_preserved base 0 (by decide)

theorem completed_copy (base : Nat → F) : completed base copy=base copy :=
  run_preserves base steps [0,copy] [] ordered copy (by simp)

theorem completed_cut_inputs (base : Nat → F) :
    (fun input => eval (completed base) (inputTerms input)) =
      (fun input => eval base (inputTerms input)) := by
  funext input
  by_cases bound : input<6
  · exact CompilerPriorFrame01.completed_inputs 6 inputTerms steps cut_support_checked base input bound
  · simp only [input_terms_outside input (Nat.le_of_not_gt bound),eval]

theorem completed_values (base : Nat → F) (one : base 0=1) (linked : base copy=base 0) (four : (4:F)≠0) :
    (fun index => expressionValue (completed base) (expressions index)) =
      SourceGraphEvaluation.values graph (fun input => eval base (inputTerms input)) := by
  have same := arbitrary_assignment_sound (completed base) ((completed_one base).trans one) four (completed_rows base linked)
  rw [completed_cut_inputs base] at same
  exact same

theorem total_round_assignment (base : Nat → F) (one : base 0=1) (linked : base copy=base 0) (four : (4:F)≠0) :
    Satisfies (completed base) originalRows.toList ∧
      (∀ input<22735,completed base (3+input)=base (3+input)) ∧
      (fun input => eval (completed base) (inputTerms input))=(fun input => eval base (inputTerms input)) ∧
      (fun index => expressionValue (completed base) (expressions index))=
        SourceGraphEvaluation.values graph (fun input => eval base (inputTerms input)) :=
  ⟨completed_rows base linked,original_inputs_preserved base,completed_cut_inputs base,completed_values base one linked four⟩
end ShielddSecurity.TransferPoseidonRound04Proof01

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.coverage_checked
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.coverage_checked

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.all_index_coverage
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.all_index_coverage

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.node_certificates
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.node_certificates

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.actual_copy_checked
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.actual_copy_checked

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.rows_coverage_checked
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.rows_coverage_checked

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.emitted_identity
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.emitted_identity

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.reverse_coverage
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.reverse_coverage

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.ordered_check
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.ordered_check

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.ordered
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.ordered

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.writes_check
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.writes_check

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.writes_lower_bound
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.writes_lower_bound

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.cut_support_checked
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.cut_support_checked

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.input_terms_outside
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.input_terms_outside

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.actual_copy_link
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.actual_copy_link

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.arbitrary_assignment_sound
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.arbitrary_assignment_sound

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.legal
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.legal

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.completed_rows
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.completed_rows

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.original_columns_preserved
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.original_columns_preserved

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.original_inputs_preserved
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.original_inputs_preserved

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.completed_one
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.completed_one

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.completed_copy
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.completed_copy

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.completed_cut_inputs
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.completed_cut_inputs

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.completed_values
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.completed_values

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonRound04Proof01.total_round_assignment
#print axioms ShielddSecurity.TransferPoseidonRound04Proof01.total_round_assignment
