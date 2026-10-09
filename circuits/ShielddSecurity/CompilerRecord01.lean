import ShielddSecurity.CompilerIndexed01

set_option maxHeartbeats 700000
set_option maxRecDepth 8192
namespace ShielddSecurity.CompilerRecord01
open Compiler

inductive Record where
  | constant (coefficient : Int)
  | input (index : Nat)
  | add (left right : Nat)
  | mul (left right : Nat)
  deriving DecidableEq

def Record.Valid (records : Array Record) (inputs index : Nat) : Record → Prop
  | .constant _ => True
  | .input witness => witness<inputs
  | .add left right => left<index ∧ right<index
  | .mul left right => left<index ∧ right<index

instance (records : Array Record) (inputs index : Nat) (record : Record) : Decidable (record.Valid records inputs index) := by
  cases record <;> unfold Record.Valid <;> infer_instance

def Record.check (records : Array Record) (inputs index : Nat) : Record → Bool
  | .constant _ => true
  | .input witness => decide (witness<inputs)
  | .add left right => decide (left<index) && decide (right<index)
  | .mul left right => decide (left<index) && decide (right<index)

theorem record_check_sound (records : Array Record) (inputs index : Nat) (record : Record)
    (checked : record.check records inputs index=true) : record.Valid records inputs index := by
  cases record with
  | constant coefficient => trivial
  | input witness => exact of_decide_eq_true checked
  | add left right => simpa only [Record.check,Record.Valid,Bool.and_eq_true,decide_eq_true_eq] using checked
  | mul left right => simpa only [Record.check,Record.Valid,Bool.and_eq_true,decide_eq_true_eq] using checked

def checkRecordAt (inputs : Nat) (records : Array Record) (index : Nat) : Bool :=
  match records[index]? with
  | none => false
  | some record => record.check records inputs index

def checkList (inputs : Nat) (records : Array Record) (start : Nat) (items : List Record) : Bool :=
  (items.zipIdx start).all (fun pair => pair.1.check records inputs pair.2)

def checkRecords (inputs : Nat) (records : Array Record) : Bool := checkList inputs records 0 records.toList

theorem checkList_append (inputs : Nat) (records : Array Record) (start : Nat) (left right : List Record) :
    checkList inputs records start (left++right)=
      (checkList inputs records start left && checkList inputs records (start+left.length) right) := by
  simp only [checkList,List.zipIdx_append,List.all_append]

def checkChunks (inputs : Nat) (records : Array Record) (start : Nat) : List (List Record) → Bool
  | [] => true
  | head::tail => checkList inputs records start head && checkChunks inputs records (start+head.length) tail

theorem checked_chunks (inputs : Nat) (records : Array Record) (start : Nat) (chunks : List (List Record))
    (checked : checkChunks inputs records start chunks=true) : checkList inputs records start chunks.flatten=true := by
  induction chunks generalizing start with
  | nil => rfl
  | cons head tail ih =>
      simp only [checkChunks,Bool.and_eq_true] at checked
      simp only [List.flatten_cons,checkList_append,checked.1,ih _ checked.2,Bool.true_and]


theorem checked_valid (inputs : Nat) (records : Array Record) (checked : checkRecords inputs records=true)
    (index : Fin records.size) : (records[index]).Valid records inputs index.val := by
  have member : (records[index],index.val) ∈ records.toList.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    rw [Array.getElem?_toList,Array.getElem?_eq_getElem index.isLt]
    rfl
  exact record_check_sound records inputs index.val _ (List.all_eq_true.mp checked _ member)

def Record.toNode (records : Array Record) (inputs index : Nat) (record : Record)
    (valid : record.Valid records inputs index) : SourceNode index :=
  match record with
  | .constant coefficient => .constant coefficient
  | .input witness => .input witness
  | .add left right => .add ⟨left,valid.1⟩ ⟨right,valid.2⟩
  | .mul left right => .mul ⟨left,valid.1⟩ ⟨right,valid.2⟩

theorem toNode_input_bound (records : Array Record) (inputs index : Nat) (record : Record)
    (valid : record.Valid records inputs index) (input : Nat)
    (found : record.toNode records inputs index valid = .input input) : input<inputs := by
  cases record <;> simp only [Record.toNode,SourceNode.input.injEq] at found
  · cases found
  · subst input; exact valid
  · cases found
  · cases found

theorem toNode_congr (records : Array Record) (inputs index : Nat) (left right : Record)
    (leftValid : left.Valid records inputs index) (rightValid : right.Valid records inputs index)
    (same : left=right) : left.toNode records inputs index leftValid=right.toNode records inputs index rightValid := by
  subst right
  rfl

def graph (inputs : Nat) (records : Array Record) (checked : checkRecords inputs records=true)
    (assertions : List (Fin records.size × Fin records.size)) (outputs : List (Fin records.size)) : SourceGraph inputs records.size :=
  ⟨fun index => (records[index]).toNode records inputs index.val (checked_valid inputs records checked index),
    fun index input found => toNode_input_bound records inputs index.val _ (checked_valid inputs records checked index) input found,
    assertions,outputs⟩


end ShielddSecurity.CompilerRecord01

set_option pp.all true in
#check @ShielddSecurity.CompilerRecord01.record_check_sound
#print axioms ShielddSecurity.CompilerRecord01.record_check_sound

set_option pp.all true in
#check @ShielddSecurity.CompilerRecord01.checkList_append
#print axioms ShielddSecurity.CompilerRecord01.checkList_append

set_option pp.all true in
#check @ShielddSecurity.CompilerRecord01.checked_chunks
#print axioms ShielddSecurity.CompilerRecord01.checked_chunks

set_option pp.all true in
#check @ShielddSecurity.CompilerRecord01.checked_valid
#print axioms ShielddSecurity.CompilerRecord01.checked_valid

set_option pp.all true in
#check @ShielddSecurity.CompilerRecord01.toNode_input_bound
#print axioms ShielddSecurity.CompilerRecord01.toNode_input_bound

set_option pp.all true in
#check @ShielddSecurity.CompilerRecord01.toNode_congr
#print axioms ShielddSecurity.CompilerRecord01.toNode_congr
