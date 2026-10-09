-- GENERATED instance of maintained first-two-proof-template.lean.txt.
import ShielddSecurity.TransferPoseidonFirstTwo02Data01
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferPoseidonFirstTwo02Proof01
open Compiler CompilerCompletion CompilerIndexed01 TransferPoseidonFirstTwo02

theorem first_order_checked : CompilerOrder.checkOrder [0,copy] [] first=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_order_checked
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_order_checked

theorem second_order_checked : CompilerOrder.checkOrder [0,copy] [] second=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.second_order_checked
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.second_order_checked

theorem first_support_checked : (emitted first).all (fun row => (row.a++row.b).all (fun term => decide (term.1<23076)))=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_support_checked
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_support_checked

theorem first_raw_support_checked : TransferPoseidonAbsorb02.originalRows.toList.all
    (fun row => (row.a++row.b).all (fun term => decide (term.1<23076 ∨ term.1=copy)))=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_raw_support_checked
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_raw_support_checked

theorem first_writes_checked : (PoseidonCompletion.writes first).all (fun column => decide (23060≤column ∧ column≤23075))=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_writes_checked
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_writes_checked

theorem second_writes_checked : (PoseidonCompletion.writes second).all (fun column => decide (23076≤column ∧ column≤23099))=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.second_writes_checked
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.second_writes_checked

theorem second_write_bounds (column : Nat) (member : column∈PoseidonCompletion.writes second) : 23076≤column ∧ column≤23099 :=
  of_decide_eq_true (List.all_eq_true.mp second_writes_checked column member)

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.second_write_bounds
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.second_write_bounds

theorem first_order : Topological [0,copy] [] first := CompilerOrder.checked_order _ _ _ first_order_checked
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_order
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_order

theorem second_order_empty : Topological [0,copy] [] second := CompilerOrder.checked_order _ _ _ second_order_checked

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.second_order_empty
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.second_order_empty

theorem second_order_prior : Topological [0,copy] (emitted first) second := by
  have fresh : ∀ row∈emitted first,∀ term∈row.a++row.b,∀ step∈second,term.1∉step.writes := by
    intro row member term present step included written
    have support := List.all_eq_true.mp first_support_checked row member
    have upper : term.1<23076 := of_decide_eq_true (List.all_eq_true.mp support term present)
    have lower := (second_write_bounds term.1 (PoseidonCompletion.mem_writes_of_step step second included term.1 written)).1
    omega
  simpa only [List.append_nil] using CompilerOrderComposition.extend [0,copy] [] (emitted first) second second_order_empty fresh

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.second_order_prior
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.second_order_prior

theorem first_second_order : Topological [0,copy] [] (first++second) :=
  CompilerOrderComposition.append [0,copy] [] first second first_order (by simpa using second_order_prior)

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_second_order
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_second_order

theorem copy_order : Topological [0,copy] (emitted (first++second)) [copyStep] := by
  simp [copyStep,TransferPoseidonAbsorb02Program01.copyStep,Topological,Step.Shape,Step.writes]

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.copy_order
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.copy_order

theorem ordered : Topological [0,copy] [] steps :=
  CompilerOrderComposition.append [0,copy] [] (first++second) [copyStep] first_second_order (by simpa using copy_order)

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.ordered
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.ordered

theorem reverse_checked : checkOriginalCoverage p copy originalRows emittedRows reverseMapping=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.reverse_checked
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.reverse_checked

theorem first_inclusion_checked : CompilerRawInclusion02.check p TransferPoseidonAbsorb02.originalRows originalRows firstMapping=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_inclusion_checked
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_inclusion_checked

theorem second_inclusion_checked : CompilerRawInclusion02.check p TransferPoseidonRound01.originalRows originalRows secondMapping=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.second_inclusion_checked
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.second_inclusion_checked

theorem actual_copy_checked : checkRowAt p originalRows 40 ⟨[(0,1),(copy,-1)],[]⟩=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.actual_copy_checked
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.actual_copy_checked

theorem rows_shape : originalRows.size=41 ∧ steps.length=31 ∧ captureIndices.toList=List.range' 322 40++[200769] := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.rows_shape
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.rows_shape

theorem boundary_checked : (List.finRange 6).all (fun column => decide
    (TransferPoseidonRound01.inputTerms column.val=TransferPoseidonAbsorb02SemanticData01.after column))=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.boundary_checked
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.boundary_checked

theorem boundary_binding (column : Fin 6) : TransferPoseidonRound01.inputTerms column.val=TransferPoseidonAbsorb02SemanticData01.after column :=
  of_decide_eq_true (List.all_eq_true.mp boundary_checked column (List.mem_finRange column))
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.boundary_binding
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.boundary_binding

theorem round0_parameters : TransferPoseidonAbsorb02SemanticData01.parameters=parameters := rfl
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.round0_parameters
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.round0_parameters

theorem round1_ark : TransferPoseidonRound01SemanticData01.parameters.ark 1=parameters.ark 1 := rfl
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.round1_ark
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.round1_ark

theorem round1_mds : TransferPoseidonRound01SemanticData01.parameters.mds=parameters.mds := rfl

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.round1_mds
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.round1_mds

theorem reverse_coverage : ∀ actual∈originalRows.toList,∃ expected∈emitted steps,
    canonical p (unoutline copy actual.a)=canonical p expected.a ∧
      canonical p (unoutline copy actual.b)=canonical p expected.b := by
  simpa only [emittedRows,Array.toList_toArray] using
    checkOriginalCoverage_sound p copy originalRows emittedRows reverseMapping reverse_checked

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.reverse_coverage
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.reverse_coverage

variable {F : Type} [Field F] [CharP F p]

theorem first_rows (rho : Nat → F) (satisfied : Satisfies rho originalRows.toList) : Satisfies rho TransferPoseidonAbsorb02.originalRows.toList :=
  CompilerRawInclusion02.checked_satisfies _ _ firstMapping first_inclusion_checked rho satisfied
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_rows
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.first_rows

theorem second_rows (rho : Nat → F) (satisfied : Satisfies rho originalRows.toList) : Satisfies rho TransferPoseidonRound01.originalRows.toList :=
  CompilerRawInclusion02.checked_satisfies _ _ secondMapping second_inclusion_checked rho satisfied

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.second_rows
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.second_rows

theorem earlier_raw_frame (base : Nat → F) (row : Row) (member : row∈TransferPoseidonAbsorb02.originalRows.toList) :
    eval (run base second) row.a=eval base row.a ∧ eval (run base second) row.b=eval base row.b := by
  have support := List.all_eq_true.mp first_raw_support_checked row member
  have outside (term : Nat×Int) (present : term∈row.a++row.b) : term.1∉PoseidonCompletion.writes second := by
    intro written
    have condition : term.1<23076 ∨ term.1=copy := of_decide_eq_true (List.all_eq_true.mp support term present)
    have bounds := second_write_bounds term.1 written
    rcases condition with before | immutable
    · omega
    · have far : copy=200692 := rfl
      omega
  constructor
  · exact PoseidonCompletion.eval_run_preserves base second row.a (by intro term present;exact outside term (List.mem_append_left _ present))
  · exact PoseidonCompletion.eval_run_preserves base second row.b (by intro term present;exact outside term (List.mem_append_right _ present))

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.earlier_raw_frame
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.earlier_raw_frame

theorem arbitrary_two_rounds (rho : Nat → F) (one : rho 0=1) (four : (4:F)≠0)
    (satisfied : Satisfies rho originalRows.toList) :
    (fun column => expressionValue rho (TransferPoseidonRound01.expressions (finalPorts column))) =
      Poseidon.rounds (Poseidon.castParameters parameters) 2
        (Poseidon.absorb (Poseidon.initial 23 4)
          (TransferPoseidonAbsorb02SemanticData01.orderedInputs.map (fun input => eval rho (TransferPoseidonAbsorb02.inputTerms input)))) := by
  have firstResult := TransferPoseidonAbsorb02SemanticProof01.arbitrary_round_sound rho one four (first_rows rho satisfied)
  have secondResult := TransferPoseidonRound01SemanticProof01.arbitrary_round_sound rho one four (second_rows rho satisfied)
  have boundary : (fun column : Fin 6 => eval rho (TransferPoseidonRound01.inputTerms column.val)) =
      (fun column => expressionValue rho (TransferPoseidonAbsorb02.expressions (TransferPoseidonAbsorb02SemanticData01.outputPorts column))) := by
    funext column
    rw [boundary_binding,TransferPoseidonAbsorb02SemanticProof01.output_binding]
    rfl
  rw [boundary,firstResult,round0_parameters] at secondResult
  exact secondResult.trans (PoseidonRoundComposition.cast_round_agrees
    TransferPoseidonRound01SemanticData01.parameters parameters 1 _ round1_ark round1_mds)

set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.arbitrary_two_rounds
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.arbitrary_two_rounds

def completed (base : Nat → F) : Nat → F := run base steps
theorem legal (base : Nat → F) : Legal base steps := by
  simp [steps,first,second,copyStep,TransferPoseidonAbsorb02Program01.materializedSteps,
    TransferPoseidonRound01Program01.materializedSteps,TransferPoseidonAbsorb02Program01.copyStep,Legal,Step.Legal]
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.legal
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.legal

theorem completed_rows (base : Nat → F) (linked : base copy=base 0) : Satisfies (completed base) originalRows.toList :=
  (original_rows_complete base steps [0,copy] originalRows.toList copy ordered (legal base)
    (by simp) (by simp) linked reverse_coverage).1
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.completed_rows
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.completed_rows

theorem writes_checked : (PoseidonCompletion.writes steps).all (fun column => decide (22738≤column))=true := by decide +kernel
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.writes_checked
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.writes_checked

theorem original_columns_preserved (base : Nat → F) (column : Nat) (bound : column<22738) : completed base column=base column := by
  apply PoseidonCompletion.run_outside
  intro written
  have lower : 22738≤column := of_decide_eq_true (List.all_eq_true.mp writes_checked column written)
  omega
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.original_columns_preserved
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.original_columns_preserved

theorem copy_preserved (base : Nat → F) : completed base copy=base copy := run_preserves base steps [0,copy] [] ordered copy (by simp)
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.copy_preserved
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.copy_preserved

theorem original_input_values (base : Nat → F) :
    (fun input => eval (completed base) (TransferPoseidonAbsorb02.inputTerms input))=(fun input => eval base (TransferPoseidonAbsorb02.inputTerms input)) := by
  funext input
  by_cases bound : input<22735
  · simp [TransferPoseidonAbsorb02.inputTerms,bound,eval,original_columns_preserved base (3+input) (by omega : 3+input<22738)]
  · simp [TransferPoseidonAbsorb02.inputTerms,bound,eval]
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.original_input_values
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.original_input_values

theorem completed_two_rounds (base : Nat → F) (one : base 0=1) (linked : base copy=base 0) (four : (4:F)≠0) :
    (fun column => expressionValue (completed base) (TransferPoseidonRound01.expressions (finalPorts column))) =
      Poseidon.rounds (Poseidon.castParameters parameters) 2
        (Poseidon.absorb (Poseidon.initial 23 4)
          (TransferPoseidonAbsorb02SemanticData01.orderedInputs.map (fun input => eval base (TransferPoseidonAbsorb02.inputTerms input)))) := by
  have result := arbitrary_two_rounds (completed base) ((original_columns_preserved base 0 (by decide)).trans one) four (completed_rows base linked)
  exact result.trans (congrArg (fun values => Poseidon.rounds (Poseidon.castParameters parameters) 2 (Poseidon.absorb (Poseidon.initial 23 4) values))
    (congrArg (fun f : Nat → F => TransferPoseidonAbsorb02SemanticData01.orderedInputs.map f) (original_input_values base)))
set_option pp.all true in
#check @ShielddSecurity.TransferPoseidonFirstTwo02Proof01.completed_two_rounds
#print axioms ShielddSecurity.TransferPoseidonFirstTwo02Proof01.completed_two_rounds

end ShielddSecurity.TransferPoseidonFirstTwo02Proof01
