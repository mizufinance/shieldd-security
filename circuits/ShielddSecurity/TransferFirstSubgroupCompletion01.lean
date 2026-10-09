import ShielddSecurity.TransferFirstSubgroupCertificates01
import ShielddSecurity.CompilerOrder
import ShielddSecurity.PoseidonCompletion

set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferFirstSubgroupCompletion01
open Compiler CompilerCompletion CompilerIndexed01 TransferFirstSubgroupData01 TransferFirstSubgroupCertificates01

variable {F : Type} [Field F] [CharP F p]

def boundary (inputs : Nat → F) (column : Nat) : F :=
  if column=0 ∨ column=copy then 1 else inputs (column-3)

def completed (inputs : Nat → F) : Nat → F := run (boundary inputs) arithmeticSteps

theorem ordered_check : CompilerOrder.checkOrder [0,copy] [] arithmeticSteps = true := by decide +kernel

theorem ordered : Topological [0,copy] [] arithmeticSteps :=
  CompilerOrder.checked_order _ _ _ ordered_check

theorem legal (base : Nat → F) : Legal base arithmeticSteps := by
  simp [arithmeticSteps,materializedSteps,Legal,Step.Legal,copyStep]

theorem completed_arithmetic (inputs : Nat → F) : Satisfies (completed inputs) arithmeticRows.toList := by
  exact (original_rows_complete (boundary inputs) arithmeticSteps [0,copy] arithmeticRows.toList copy
    ordered (legal _) (by simp) (by simp) (by simp [boundary]) arithmetic_reverse_coverage).1

theorem writes_check : (PoseidonCompletion.writes arithmeticSteps).all (fun c => decide (22738 ≤ c))=true := by
  decide +kernel

theorem writes_lower_bound (column : Nat) (member : column ∈ PoseidonCompletion.writes arithmeticSteps) :
    22738 ≤ column := of_decide_eq_true (List.all_eq_true.mp writes_check column member)

theorem original_input_preserved (inputs : Nat → F) (input : Nat) (bound : input<22735) :
    completed inputs (3+input)=inputs input := by
  have outside : 3+input ∉ PoseidonCompletion.writes arithmeticSteps := by
    intro member
    have lower := writes_lower_bound _ member
    omega
  have preserved := PoseidonCompletion.run_outside (boundary inputs) arithmeticSteps (3+input) outside
  change run (boundary inputs) arithmeticSteps (3+input) = inputs input
  rw [preserved]
  have copyOutside : 3+input ≠ copy := by unfold copy; omega
  simp [boundary,copyOutside]

theorem completed_one (inputs : Nat → F) : completed inputs 0=1 := by
  have preserved := run_preserves (boundary inputs) arithmeticSteps [0,copy] [] ordered 0 (by simp)
  simpa [completed,boundary] using preserved

theorem completed_copy (inputs : Nat → F) : completed inputs copy=1 := by
  have preserved := run_preserves (boundary inputs) arithmeticSteps [0,copy] [] ordered copy (by simp)
  simpa [completed,boundary] using preserved

theorem completed_inputs (inputs : Nat → F) (input : Nat) (bound : input<22735) :
    eval (completed inputs) (inputTerms input)=inputs input := by
  simpa [inputTerms,eval] using original_input_preserved inputs input bound

theorem completed_values (inputs : Nat → F) (four : (4:F)≠0) :
    (fun index => expressionValue (completed inputs) (expressions index)) =
      SourceGraphEvaluation.values graph inputs := by
  have unoutlined := unoutline_rows_sound (completed inputs) copy arithmeticRows.toList
    (completed_arithmetic inputs) (checkRowAt_sound p arithmeticRows 64 _ arithmetic_copy_checked)
  have computes (index : Fin 80) := node_certificate_sound (unoutlineRows copy arithmeticRows.toList)
    inputTerms (graph.prior expressions index) (graph.node index) (expressions index)
    (node_certificates index) (completed inputs) (completed_one inputs) four unoutlined
  apply Eq.symm
  apply SourceGraphEvaluation.computing_values_unique
  intro index
  rw [computes index]
  cases found : graph.node index with
  | input input =>
      simp only [sourceValue]
      exact completed_inputs inputs input (graph.inputBound index input found)
  | constant coefficient => rfl
  | add left right => rfl
  | mul left right => rfl

end ShielddSecurity.TransferFirstSubgroupCompletion01

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCompletion01.ordered_check
#print axioms ShielddSecurity.TransferFirstSubgroupCompletion01.ordered_check

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCompletion01.ordered
#print axioms ShielddSecurity.TransferFirstSubgroupCompletion01.ordered

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCompletion01.legal
#print axioms ShielddSecurity.TransferFirstSubgroupCompletion01.legal

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCompletion01.completed_arithmetic
#print axioms ShielddSecurity.TransferFirstSubgroupCompletion01.completed_arithmetic

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCompletion01.writes_check
#print axioms ShielddSecurity.TransferFirstSubgroupCompletion01.writes_check

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCompletion01.writes_lower_bound
#print axioms ShielddSecurity.TransferFirstSubgroupCompletion01.writes_lower_bound

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCompletion01.original_input_preserved
#print axioms ShielddSecurity.TransferFirstSubgroupCompletion01.original_input_preserved

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCompletion01.completed_one
#print axioms ShielddSecurity.TransferFirstSubgroupCompletion01.completed_one

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCompletion01.completed_copy
#print axioms ShielddSecurity.TransferFirstSubgroupCompletion01.completed_copy

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCompletion01.completed_inputs
#print axioms ShielddSecurity.TransferFirstSubgroupCompletion01.completed_inputs

set_option pp.all true in
#check @ShielddSecurity.TransferFirstSubgroupCompletion01.completed_values
#print axioms ShielddSecurity.TransferFirstSubgroupCompletion01.completed_values
