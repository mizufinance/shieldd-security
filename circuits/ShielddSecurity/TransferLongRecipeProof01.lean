import ShielddSecurity.TransferLongRecipeData01
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.TransferLongRecipeProof01
open Compiler CompilerIndexed01 TransferLongRecipeData01
variable {F : Type} [Field F] [CharP F p]

theorem four_nonzero : (4:F)≠0 := by
  intro zero
  have castZero : ((4:Nat):F)=((0:Nat):F) := by simpa using zero
  have congruent := (CharP.cast_eq_iff_mod_eq F p).mp castZero
  have small : 4<p := by decide
  have impossible : (4:Nat)=0 := by
    simpa only [Nat.mod_eq_of_lt small,Nat.zero_mod] using congruent
  omega

theorem compiled_values (rho : Nat → F) (one : rho 0=1) :
    (fun index => expressionValue rho (expressions index)) =
      SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) :=
  CompilerGraphEvaluationSoundness.compiled_values_eq_evaluation graph [] inputTerms expressions
    node_certificates rho one four_nonzero (by intro row member;cases member)

theorem actual_row_equalities :
    canonical p originalRow.a=canonical p expectedRow.a ∧
      canonical p originalRow.b=canonical p expectedRow.b := by
  have checked := consumer_checked
  change decide (canonical p originalRow.a=canonical p expectedRow.a ∧
    canonical p originalRow.b=canonical p expectedRow.b)=true at checked
  exact of_decide_eq_true checked

theorem source_assertion_sound (rho : Nat → F) (one : rho 0=1)
    (satisfied : Satisfies rho originalRows.toList) :
    SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) leftPort =
      SourceGraphEvaluation.values graph (fun input => eval rho (inputTerms input)) rightPort := by
  have equality := checked_assertion_sound rho originalRows.toList (terms leftPort) (terms rightPort)
    satisfied (checkRowAt_sound p originalRows 0 expectedRow consumer_checked)
  have same := compiled_values rho one
  have left := congrFun same leftPort
  have right := congrFun same rightPort
  change eval rho (terms leftPort)=_ at left
  change eval rho (terms rightPort)=_ at right
  exact left.symm.trans (equality.trans right)

def assignment (inputs : Nat → F) (column : Nat) : F :=
  if column=0 then 1 else inputs (column-3)

theorem assignment_one (inputs : Nat → F) : assignment inputs 0=1 := rfl

theorem input_preserved (inputs : Nat → F) (input : Nat) :
    assignment inputs (3+input)=inputs input := by
  have nonzero : 3+input≠0 := by omega
  have index : 3+input-3=input := by omega
  simp only [assignment,nonzero,if_false,index]

theorem inputs_evaluate (inputs : Nat → F) :
    (fun input => eval (assignment inputs) (inputTerms input))=inputs := by
  funext input
  simp only [inputTerms,eval,Int.cast_one,one_mul,zero_add,add_zero]
  exact input_preserved inputs input

/-- The source assertion premise is an independent arithmetic-graph property;
this bounded chain prototype does not derive native Transfer legality. -/
theorem constructive_consumer_complete (inputs : Nat → F)
    (truth : SourceGraphEvaluation.values graph inputs leftPort =
      SourceGraphEvaluation.values graph inputs rightPort) :
    Satisfies (assignment inputs) originalRows.toList ∧
      (∀ input < 22735,assignment inputs (3+input)=inputs input) ∧ assignment inputs 0=1 := by
  have same := compiled_values (assignment inputs) (assignment_one inputs)
  rw [inputs_evaluate inputs] at same
  have left := congrFun same leftPort
  have right := congrFun same rightPort
  change eval (assignment inputs) (terms leftPort)=_ at left
  change eval (assignment inputs) (terms rightPort)=_ at right
  have equality := left.trans (truth.trans right.symm)
  have expected : Square (eval (assignment inputs) expectedRow.a) (eval (assignment inputs) expectedRow.b) := by
    change Square (eval (assignment inputs) (subtract (terms leftPort) (terms rightPort))) (eval (assignment inputs) [])
    simp only [eval_subtract,equality,sub_self,eval,Square,zero_mul]
  have actual : Square (eval (assignment inputs) originalRow.a) (eval (assignment inputs) originalRow.b) := by
    rw [canonical_equal (assignment inputs) _ _ actual_row_equalities.1,
        canonical_equal (assignment inputs) _ _ actual_row_equalities.2]
    exact expected
  refine ⟨?_,fun input _ => input_preserved inputs input,assignment_one inputs⟩
  intro row member
  have sameRow : row=originalRow := by simpa only [originalRows,Array.toList,List.mem_singleton] using member
  subst row
  exact actual
end ShielddSecurity.TransferLongRecipeProof01

set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipeProof01.four_nonzero
#print axioms ShielddSecurity.TransferLongRecipeProof01.four_nonzero

set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipeProof01.compiled_values
#print axioms ShielddSecurity.TransferLongRecipeProof01.compiled_values

set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipeProof01.actual_row_equalities
#print axioms ShielddSecurity.TransferLongRecipeProof01.actual_row_equalities

set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipeProof01.source_assertion_sound
#print axioms ShielddSecurity.TransferLongRecipeProof01.source_assertion_sound

set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipeProof01.assignment_one
#print axioms ShielddSecurity.TransferLongRecipeProof01.assignment_one

set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipeProof01.input_preserved
#print axioms ShielddSecurity.TransferLongRecipeProof01.input_preserved

set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipeProof01.inputs_evaluate
#print axioms ShielddSecurity.TransferLongRecipeProof01.inputs_evaluate

set_option pp.all true in
#check @ShielddSecurity.TransferLongRecipeProof01.constructive_consumer_complete
#print axioms ShielddSecurity.TransferLongRecipeProof01.constructive_consumer_complete
