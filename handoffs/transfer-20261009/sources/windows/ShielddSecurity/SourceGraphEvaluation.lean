import ShielddSecurity.Compiler

set_option maxHeartbeats 150000
set_option maxRecDepth 4096

namespace ShielddSecurity.SourceGraphEvaluation
open Compiler
variable {F : Type} [Field F]

/-! Total evaluation for the existing typed arithmetic source graph. Recursion
is symbolic on earlier node indices. Assertion truth is a separate owned
algorithm obligation; this evaluator never presumes a satisfying assignment. -/
def values {inputs nodes : Nat} (graph : SourceGraph inputs nodes)
    (inputValues : Nat → F) (index : Fin nodes) : F :=
  sourceValue inputValues
    (fun previous : Fin index.val => values graph inputValues
      ⟨previous.val, Nat.lt_trans previous.isLt index.isLt⟩) (graph.node index)
termination_by index.val
decreasing_by exact previous.isLt

theorem values_compute {inputs nodes : Nat} (graph : SourceGraph inputs nodes)
    (inputValues : Nat → F) (index : Fin nodes) :
    values graph inputValues index =
      sourceValue inputValues (graph.prior (values graph inputValues) index) (graph.node index) := by
  rw [values]
  rfl

theorem computing_values_unique {inputs nodes : Nat} (graph : SourceGraph inputs nodes)
    (inputValues : Nat → F) (reference : Fin nodes → F)
    (computes : ∀ index, reference index =
      sourceValue inputValues (graph.prior reference index) (graph.node index)) :
    values graph inputValues = reference :=
  graph_values_unique graph inputValues (values graph inputValues) reference
    (values_compute graph inputValues) computes

theorem satisfies_iff_assertions {inputs nodes : Nat} (graph : SourceGraph inputs nodes)
    (inputValues : Nat → F) :
    GraphSatisfies graph inputValues (values graph inputValues) ↔
      ∀ assertion ∈ graph.assertions,
        values graph inputValues assertion.1 = values graph inputValues assertion.2 :=
  ⟨fun satisfied => satisfied.2, fun assertions => ⟨values_compute graph inputValues, assertions⟩⟩

theorem outputs_unique {inputs nodes : Nat} (graph : SourceGraph inputs nodes)
    (inputValues : Nat → F) (reference : Fin nodes → F)
    (computes : ∀ index, reference index =
      sourceValue inputValues (graph.prior reference index) (graph.node index)) :
    graph.outputs.map (values graph inputValues) = graph.outputs.map reference :=
  congrArg (fun computed : Fin nodes → F => graph.outputs.map computed)
    (computing_values_unique graph inputValues reference computes)

theorem computing_values_exist {inputs nodes : Nat} (graph : SourceGraph inputs nodes)
    (inputValues : Nat → F) :
    ∃ computed : Fin nodes → F,
      (∀ index, computed index =
        sourceValue inputValues (graph.prior computed index) (graph.node index)) ∧
      ∀ reference : Fin nodes → F,
        (∀ index, reference index =
          sourceValue inputValues (graph.prior reference index) (graph.node index)) →
        computed = reference :=
  ⟨values graph inputValues, values_compute graph inputValues,
    computing_values_unique graph inputValues⟩

set_option pp.all true in
#check @values_compute
#print axioms values_compute
set_option pp.all true in
#check @computing_values_unique
#print axioms computing_values_unique
set_option pp.all true in
#check @satisfies_iff_assertions
#print axioms satisfies_iff_assertions
set_option pp.all true in
#check @outputs_unique
#print axioms outputs_unique
set_option pp.all true in
#check @computing_values_exist
#print axioms computing_values_exist

end ShielddSecurity.SourceGraphEvaluation
