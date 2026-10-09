import ShielddSecurity.SourceGraphEvaluation
namespace ShielddSecurity.SourceGraphNodeValues01
open Compiler
variable {F : Type} [Field F]

theorem input_value {inputs nodes : Nat} (graph : SourceGraph inputs nodes) (values : Nat → F)
    (index : Fin nodes) (input : Nat) (identity : graph.node index=.input input) :
    SourceGraphEvaluation.values graph values index=values input := by
  rw [SourceGraphEvaluation.values_compute,identity]
  rfl

theorem constant_value {inputs nodes : Nat} (graph : SourceGraph inputs nodes) (values : Nat → F)
    (index : Fin nodes) (coefficient : Int) (identity : graph.node index=.constant coefficient) :
    SourceGraphEvaluation.values graph values index=(coefficient:F) := by
  rw [SourceGraphEvaluation.values_compute,identity]
  rfl

theorem add_value {inputs nodes : Nat} (graph : SourceGraph inputs nodes) (values : Nat → F)
    (index : Fin nodes) (left right : Fin index.val) (identity : graph.node index=.add left right) :
    SourceGraphEvaluation.values graph values index=
      SourceGraphEvaluation.values graph values ⟨left.val,Nat.lt_trans left.isLt index.isLt⟩+
      SourceGraphEvaluation.values graph values ⟨right.val,Nat.lt_trans right.isLt index.isLt⟩ := by
  rw [SourceGraphEvaluation.values_compute,identity]
  rfl

theorem mul_value {inputs nodes : Nat} (graph : SourceGraph inputs nodes) (values : Nat → F)
    (index : Fin nodes) (left right : Fin index.val) (identity : graph.node index=.mul left right) :
    SourceGraphEvaluation.values graph values index=
      SourceGraphEvaluation.values graph values ⟨left.val,Nat.lt_trans left.isLt index.isLt⟩*
      SourceGraphEvaluation.values graph values ⟨right.val,Nat.lt_trans right.isLt index.isLt⟩ := by
  rw [SourceGraphEvaluation.values_compute,identity]
  rfl
end ShielddSecurity.SourceGraphNodeValues01

set_option pp.all true in
#check @ShielddSecurity.SourceGraphNodeValues01.input_value
#print axioms ShielddSecurity.SourceGraphNodeValues01.input_value

set_option pp.all true in
#check @ShielddSecurity.SourceGraphNodeValues01.constant_value
#print axioms ShielddSecurity.SourceGraphNodeValues01.constant_value

set_option pp.all true in
#check @ShielddSecurity.SourceGraphNodeValues01.add_value
#print axioms ShielddSecurity.SourceGraphNodeValues01.add_value

set_option pp.all true in
#check @ShielddSecurity.SourceGraphNodeValues01.mul_value
#print axioms ShielddSecurity.SourceGraphNodeValues01.mul_value
