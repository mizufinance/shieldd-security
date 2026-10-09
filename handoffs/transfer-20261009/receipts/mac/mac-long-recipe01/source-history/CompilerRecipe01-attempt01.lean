import ShielddSecurity.CompilerGraphEvaluationSoundness

set_option maxHeartbeats 700000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerRecipe01
open Compiler

inductive Record where
  | constant (coefficient : Int)
  | input (index : Nat)
  | add (left right : Nat)
  | scaleLeft (left right : Nat) (coefficient : Int)
  deriving DecidableEq

def Record.Valid (records : Array Record) (inputs index : Nat) : Record → Prop
  | .constant _ => True
  | .input input => input<inputs
  | .add left right => left<index ∧ right<index
  | .scaleLeft left right coefficient => left<index ∧ right<index ∧ records[left]?=some (.constant coefficient)

instance (records : Array Record) (inputs index : Nat) (record : Record) : Decidable (record.Valid records inputs index) := by
  cases record <;> unfold Record.Valid <;> infer_instance

def checkRecords (inputs : Nat) (records : Array Record) : Bool :=
  (List.finRange records.size).all (fun index => decide ((records[index]).Valid records inputs index.val))

theorem checked_valid (inputs : Nat) (records : Array Record) (checked : checkRecords inputs records=true)
    (index : Fin records.size) : (records[index]).Valid records inputs index.val :=
  of_decide_eq_true (List.all_eq_true.mp checked index (List.mem_finRange index))

def Record.toNode (records : Array Record) (inputs index : Nat) (record : Record)
    (valid : record.Valid records inputs index) : SourceNode index :=
  match record with
  | .constant coefficient => .constant coefficient
  | .input input => .input input
  | .add left right => .add ⟨left,valid.1⟩ ⟨right,valid.2⟩
  | .scaleLeft left right _ => .mul ⟨left,valid.1⟩ ⟨right,valid.2.1⟩

theorem toNode_input_bound (records : Array Record) (inputs index : Nat) (record : Record)
    (valid : record.Valid records inputs index) (input : Nat)
    (found : record.toNode records inputs index valid = .input input) : input<inputs := by
  cases record <;> simp only [Record.toNode,SourceNode.input.injEq] at found
  · cases found
  · subst input; exact valid
  · cases found
  · cases found

def graph (inputs : Nat) (records : Array Record) (checked : checkRecords inputs records=true)
    (assertions : List (Fin records.size × Fin records.size)) (outputs : List (Fin records.size)) : SourceGraph inputs records.size :=
  ⟨fun index => (records[index]).toNode records inputs index.val (checked_valid inputs records checked index),
    fun index input found => toNode_input_bound records inputs index.val _ (checked_valid inputs records checked index) input found,
    assertions,outputs⟩

end ShielddSecurity.CompilerRecipe01
set_option pp.all true in
#check @ShielddSecurity.CompilerRecipe01.checked_valid
#print axioms ShielddSecurity.CompilerRecipe01.checked_valid
set_option pp.all true in
#check @ShielddSecurity.CompilerRecipe01.toNode_input_bound
#print axioms ShielddSecurity.CompilerRecipe01.toNode_input_bound
