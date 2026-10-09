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

def Record.check (records : Array Record) (inputs index : Nat) : Record → Bool
  | .constant _ => true
  | .input witness => decide (witness<inputs)
  | .add left right => decide (left<index) && decide (right<index)
  | .scaleLeft left right coefficient =>
      decide (left<index) && decide (right<index) &&
      match records[left]? with
      | some (.constant actual) => decide (actual=coefficient)
      | _ => false

theorem record_check_sound (records : Array Record) (inputs index : Nat) (record : Record)
    (checked : record.check records inputs index=true) : record.Valid records inputs index := by
  cases record with
  | constant coefficient => trivial
  | input witness => exact of_decide_eq_true checked
  | add left right => simpa only [Record.check,Record.Valid,Bool.and_eq_true,decide_eq_true_eq] using checked
  | scaleLeft left right coefficient =>
      simp only [Record.check,Bool.and_eq_true,decide_eq_true_eq] at checked
      refine ⟨checked.1.1,checked.1.2,?_⟩
      cases found : records[left]? with
      | none => simp [found] at checked
      | some earlier =>
          cases earlier <;> simp [found] at checked
          next actual => simpa [found,checked.2]

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
  | .scaleLeft left right _ => .mul ⟨left,valid.1⟩ ⟨right,valid.2.1⟩

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
  rw [linearValues]
  split <;> simp_all

theorem node_certificate (p inputs : Nat) (records : Array Record) (checked : checkRecords inputs records=true)
    (inputTerms : Nat → Linear) (assertions : List (Fin records.size × Fin records.size))
    (outputs : List (Fin records.size)) (index : Fin records.size) :
    NodeCertificate p [] inputTerms
      ((graph inputs records checked assertions outputs).prior
        (fun i => Expression.linear (linearValues inputs records checked inputTerms i)) index)
      ((graph inputs records checked assertions outputs).node index)
      (.linear (linearValues inputs records checked inputTerms index)) := by
  have valid := checked_valid inputs records checked index
  cases found : records[index] with
  | constant coefficient =>
      have output := linearValues_constant inputs records checked inputTerms index coefficient found
      have nodeIdentity : (graph inputs records checked assertions outputs).node index = .constant coefficient :=
        toNode_congr records inputs index.val _ (.constant coefficient) (checked_valid inputs records checked index) trivial found
      simpa only [nodeIdentity,output] using
        (NodeCertificate.constant (p:=p) (rows:=[]) (inputTerms:=inputTerms)
          (earlier:=(graph inputs records checked assertions outputs).prior
            (fun i => Expression.linear (linearValues inputs records checked inputTerms i)) index)
          coefficient [(0,coefficient)] rfl)
  | input witness =>
      have output : linearValues inputs records checked inputTerms index=inputTerms witness := by
        rw [linearValues]
        split <;> simp_all
        all_goals rfl
      have nodeIdentity : (graph inputs records checked assertions outputs).node index = .input witness :=
        toNode_congr records inputs index.val _ (.input witness) (checked_valid inputs records checked index) (by simpa only [found] using valid) found
      simpa only [nodeIdentity,output] using
        (NodeCertificate.input (p:=p) (rows:=[]) (inputTerms:=inputTerms)
          (earlier:=(graph inputs records checked assertions outputs).prior
            (fun i => Expression.linear (linearValues inputs records checked inputTerms i)) index)
          witness (inputTerms witness) rfl)
  | add left right =>
      rw [found] at valid
      let l : Fin index.val := ⟨left,valid.1⟩
      let r : Fin index.val := ⟨right,valid.2⟩
      let x := linearValues inputs records checked inputTerms ⟨left,Nat.lt_trans valid.1 index.isLt⟩
      let y := linearValues inputs records checked inputTerms ⟨right,Nat.lt_trans valid.2 index.isLt⟩
      have output : linearValues inputs records checked inputTerms index=x++y := by
        rw [linearValues]
        split <;> simp_all
        all_goals rfl
      have nodeIdentity : (graph inputs records checked assertions outputs).node index = .add l r :=
        toNode_congr records inputs index.val _ (.add left right) (checked_valid inputs records checked index) valid found
      simpa only [nodeIdentity,output] using
        (NodeCertificate.add (p:=p) (rows:=[]) (inputTerms:=inputTerms)
          (earlier:=(graph inputs records checked assertions outputs).prior
            (fun i => Expression.linear (linearValues inputs records checked inputTerms i)) index)
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
          (fun i => Expression.linear (linearValues inputs records checked inputTerms i)) index l = Expression.linear [(0,coefficient)] := by
        simpa only [SourceGraph.prior] using congrArg Expression.linear leftValue
      have output : linearValues inputs records checked inputTerms index=scaleLinear coefficient y := by
        rw [linearValues]
        split <;> simp_all
        all_goals rfl
      have nodeIdentity : (graph inputs records checked assertions outputs).node index = .mul l r :=
        toNode_congr records inputs index.val _ (.scaleLeft left right coefficient) (checked_valid inputs records checked index) valid found
      simpa only [nodeIdentity,output] using
        (NodeCertificate.foldedLeft (p:=p) (rows:=[]) (inputTerms:=inputTerms)
          (earlier:=(graph inputs records checked assertions outputs).prior
            (fun i => Expression.linear (linearValues inputs records checked inputTerms i)) index)
          l r [(0,coefficient)] y (scaleLinear coefficient y) coefficient leftIdentity rfl rfl rfl)

def fuelValues (records : Array Record) (inputTerms : Nat → Linear) : Nat → Nat → Linear
  | 0,_ => []
  | fuel+1,index =>
      match records[index]? with
      | none => []
      | some (.constant coefficient) => [(0,coefficient)]
      | some (.input witness) => inputTerms witness
      | some (.add left right) => fuelValues records inputTerms fuel left ++ fuelValues records inputTerms fuel right
      | some (.scaleLeft _ right coefficient) => scaleLinear coefficient (fuelValues records inputTerms fuel right)

theorem fuel_agrees (inputs : Nat) (records : Array Record) (checked : checkRecords inputs records=true)
    (inputTerms : Nat → Linear) (fuel : Nat) (index : Fin records.size) (enough : index.val<fuel) :
    fuelValues records inputTerms fuel index.val=linearValues inputs records checked inputTerms index := by
  induction fuel generalizing index with
  | zero => omega
  | succ remaining ih =>
      have valid := checked_valid inputs records checked index
      cases found : records[index] with
      | constant coefficient =>
          have foundNat : records[index.val]=.constant coefficient := by simpa only [Fin.getElem_fin] using found
          rw [linearValues_constant inputs records checked inputTerms index coefficient found]
          simp only [fuelValues,Array.getElem?_eq_getElem index.isLt,foundNat]
      | input witness =>
          have foundNat : records[index.val]=.input witness := by simpa only [Fin.getElem_fin] using found
          have output : linearValues inputs records checked inputTerms index=inputTerms witness := by
            rw [linearValues]
            split <;> simp_all
          rw [output]
          simp only [fuelValues,Array.getElem?_eq_getElem index.isLt,foundNat]
      | add left right =>
          have foundNat : records[index.val]=.add left right := by simpa only [Fin.getElem_fin] using found
          rw [found] at valid
          let l : Fin records.size := ⟨left,Nat.lt_trans valid.1 index.isLt⟩
          let r : Fin records.size := ⟨right,Nat.lt_trans valid.2 index.isLt⟩
          have leftAgree := ih l (by change left<remaining; have h:=valid.1; omega)
          have rightAgree := ih r (by change right<remaining; have h:=valid.2; omega)
          have output : linearValues inputs records checked inputTerms index =
              linearValues inputs records checked inputTerms l ++ linearValues inputs records checked inputTerms r := by
            rw [linearValues]
            split <;> simp_all
            all_goals rfl
          rw [output]
          simpa only [fuelValues,Array.getElem?_eq_getElem index.isLt,foundNat] using congrArg₂ List.append leftAgree rightAgree
      | scaleLeft left right coefficient =>
          have foundNat : records[index.val]=.scaleLeft left right coefficient := by simpa only [Fin.getElem_fin] using found
          rw [found] at valid
          let r : Fin records.size := ⟨right,Nat.lt_trans valid.2.1 index.isLt⟩
          have rightAgree := ih r (by change right<remaining; have h:=valid.2.1; omega)
          have output : linearValues inputs records checked inputTerms index =
              scaleLinear coefficient (linearValues inputs records checked inputTerms r) := by
            rw [linearValues]
            split <;> simp_all
            all_goals rfl
          rw [output]
          simpa only [fuelValues,Array.getElem?_eq_getElem index.isLt,foundNat] using congrArg (scaleLinear coefficient) rightAgree

theorem fuel_stable (inputs : Nat) (records : Array Record) (checked : checkRecords inputs records=true)
    (inputTerms : Nat → Linear) (first second : Nat) (index : Fin records.size)
    (firstEnough : index.val<first) (secondEnough : index.val<second) :
    fuelValues records inputTerms first index.val=fuelValues records inputTerms second index.val :=
  (fuel_agrees inputs records checked inputTerms first index firstEnough).trans
    (fuel_agrees inputs records checked inputTerms second index secondEnough).symm

theorem fuel_node_certificate (p inputs : Nat) (records : Array Record) (checked : checkRecords inputs records=true)
    (inputTerms : Nat → Linear) (assertions : List (Fin records.size × Fin records.size))
    (outputs : List (Fin records.size)) (fuel : Nat) (enough : records.size≤fuel) (index : Fin records.size) :
    NodeCertificate p [] inputTerms
      ((graph inputs records checked assertions outputs).prior
        (fun i => .linear (fuelValues records inputTerms fuel i.val)) index)
      ((graph inputs records checked assertions outputs).node index)
      (.linear (fuelValues records inputTerms fuel index.val)) := by
  have same : (fun i : Fin records.size => Expression.linear (fuelValues records inputTerms fuel i.val)) =
      (fun i => Expression.linear (linearValues inputs records checked inputTerms i)) := by
    funext i
    exact congrArg Expression.linear (fuel_agrees inputs records checked inputTerms fuel i (Nat.lt_of_lt_of_le i.isLt enough))
  rw [same,fuel_agrees inputs records checked inputTerms fuel index (Nat.lt_of_lt_of_le index.isLt enough)]
  exact node_certificate p inputs records checked inputTerms assertions outputs index

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

set_option pp.all true in
#check @ShielddSecurity.CompilerRecipe01.toNode_congr
#print axioms ShielddSecurity.CompilerRecipe01.toNode_congr

set_option pp.all true in
#check @ShielddSecurity.CompilerRecipe01.record_check_sound
#print axioms ShielddSecurity.CompilerRecipe01.record_check_sound

set_option pp.all true in
#check @ShielddSecurity.CompilerRecipe01.checkList_append
#print axioms ShielddSecurity.CompilerRecipe01.checkList_append
set_option pp.all true in
#check @ShielddSecurity.CompilerRecipe01.checked_chunks
#print axioms ShielddSecurity.CompilerRecipe01.checked_chunks

set_option pp.all true in
#check @ShielddSecurity.CompilerRecipe01.fuel_agrees
#print axioms ShielddSecurity.CompilerRecipe01.fuel_agrees

set_option pp.all true in
#check @ShielddSecurity.CompilerRecipe01.fuel_stable
#print axioms ShielddSecurity.CompilerRecipe01.fuel_stable

set_option pp.all true in
#check @ShielddSecurity.CompilerRecipe01.fuel_node_certificate
#print axioms ShielddSecurity.CompilerRecipe01.fuel_node_certificate
