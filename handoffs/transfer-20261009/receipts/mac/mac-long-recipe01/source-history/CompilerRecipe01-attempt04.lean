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
  | .input witness => witness<inputs
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
  | .input witness => .input witness
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

def linearValues (inputs : Nat) (records : Array Record) (checked : checkRecords inputs records=true)
    (inputTerms : Nat → Linear) (index : Fin records.size) : Linear :=
  match found : records[index] with
  | .constant coefficient => [(0,coefficient)]
  | .input witness => inputTerms witness
  | .add left right =>
      linearValues inputs records checked inputTerms
        ⟨left,by have v:=checked_valid inputs records checked index; rw [found] at v; exact Nat.lt_trans v.1 index.isLt⟩ ++
      linearValues inputs records checked inputTerms
        ⟨right,by have v:=checked_valid inputs records checked index; rw [found] at v; exact Nat.lt_trans v.2 index.isLt⟩
  | .scaleLeft left right coefficient =>
      scaleLinear coefficient (linearValues inputs records checked inputTerms
        ⟨right,by have v:=checked_valid inputs records checked index; rw [found] at v; exact Nat.lt_trans v.2.1 index.isLt⟩)
termination_by index.val
decreasing_by
  all_goals have v:=checked_valid inputs records checked index; rw [found] at v
  all_goals first | exact v.1 | exact v.2 | exact v.2.1

theorem linearValues_constant (inputs : Nat) (records : Array Record) (checked : checkRecords inputs records=true)
    (inputTerms : Nat → Linear) (index : Fin records.size) (coefficient : Int)
    (found : records[index]=.constant coefficient) :
    linearValues inputs records checked inputTerms index=[(0,coefficient)] := by
  rw [linearValues,found]

theorem node_certificate (p inputs : Nat) (records : Array Record) (checked : checkRecords inputs records=true)
    (inputTerms : Nat → Linear) (assertions : List (Fin records.size × Fin records.size))
    (outputs : List (Fin records.size)) (index : Fin records.size) :
    NodeCertificate p [] inputTerms
      ((graph inputs records checked assertions outputs).prior
        (fun i => .linear (linearValues inputs records checked inputTerms i)) index)
      ((graph inputs records checked assertions outputs).node index)
      (.linear (linearValues inputs records checked inputTerms index)) := by
  have valid := checked_valid inputs records checked index
  cases found : records[index] with
  | constant coefficient =>
      have output := linearValues_constant inputs records checked inputTerms index coefficient found
      simpa only [graph,Record.toNode,found,output] using
        (NodeCertificate.constant (p:=p) (rows:=[]) (inputTerms:=inputTerms)
          (earlier:=(graph inputs records checked assertions outputs).prior
            (fun i => .linear (linearValues inputs records checked inputTerms i)) index)
          coefficient [(0,coefficient)] rfl)
  | input witness =>
      have output : linearValues inputs records checked inputTerms index=inputTerms witness := by rw [linearValues,found]
      simpa only [graph,Record.toNode,found,output] using
        (NodeCertificate.input (p:=p) (rows:=[]) (inputTerms:=inputTerms)
          (earlier:=(graph inputs records checked assertions outputs).prior
            (fun i => .linear (linearValues inputs records checked inputTerms i)) index)
          witness (inputTerms witness) rfl)
  | add left right =>
      rw [found] at valid
      let l : Fin index.val := ⟨left,valid.1⟩
      let r : Fin index.val := ⟨right,valid.2⟩
      let x := linearValues inputs records checked inputTerms ⟨left,Nat.lt_trans valid.1 index.isLt⟩
      let y := linearValues inputs records checked inputTerms ⟨right,Nat.lt_trans valid.2 index.isLt⟩
      have output : linearValues inputs records checked inputTerms index=x++y := by rw [linearValues,found]
      simpa only [graph,Record.toNode,found,output] using
        (NodeCertificate.add (p:=p) (rows:=[]) (inputTerms:=inputTerms)
          (earlier:=(graph inputs records checked assertions outputs).prior
            (fun i => .linear (linearValues inputs records checked inputTerms i)) index)
          l r x y (x++y) rfl rfl rfl)
  | scaleLeft left right coefficient =>
      rw [found] at valid
      let l : Fin index.val := ⟨left,valid.1⟩
      let r : Fin index.val := ⟨right,valid.2.1⟩
      let gl : Fin records.size := ⟨left,Nat.lt_trans valid.1 index.isLt⟩
      let y := linearValues inputs records checked inputTerms ⟨right,Nat.lt_trans valid.2.1 index.isLt⟩
      have constantFound : records[gl]=.constant coefficient := by
        have h := valid.2.2
        rw [Array.getElem?_eq_getElem gl.isLt] at h
        exact Option.some.inj h
      have leftValue := linearValues_constant inputs records checked inputTerms gl coefficient constantFound
      have leftIdentity : (graph inputs records checked assertions outputs).prior
          (fun i => .linear (linearValues inputs records checked inputTerms i)) index l = .linear [(0,coefficient)] := by
        simpa only [SourceGraph.prior] using congrArg Expression.linear leftValue
      have output : linearValues inputs records checked inputTerms index=scaleLinear coefficient y := by rw [linearValues,found]
      simpa only [graph,Record.toNode,found,output] using
        (NodeCertificate.foldedLeft (p:=p) (rows:=[]) (inputTerms:=inputTerms)
          (earlier:=(graph inputs records checked assertions outputs).prior
            (fun i => .linear (linearValues inputs records checked inputTerms i)) index)
          l r [(0,coefficient)] y (scaleLinear coefficient y) coefficient leftIdentity rfl rfl rfl)

end ShielddSecurity.CompilerRecipe01
set_option pp.all true in
#check @ShielddSecurity.CompilerRecipe01.checked_valid
#print axioms ShielddSecurity.CompilerRecipe01.checked_valid
set_option pp.all true in
#check @ShielddSecurity.CompilerRecipe01.toNode_input_bound
#print axioms ShielddSecurity.CompilerRecipe01.toNode_input_bound

set_option pp.all true in
#check @ShielddSecurity.CompilerRecipe01.linearValues_constant
#print axioms ShielddSecurity.CompilerRecipe01.linearValues_constant

set_option pp.all true in
#check @ShielddSecurity.CompilerRecipe01.node_certificate
#print axioms ShielddSecurity.CompilerRecipe01.node_certificate
