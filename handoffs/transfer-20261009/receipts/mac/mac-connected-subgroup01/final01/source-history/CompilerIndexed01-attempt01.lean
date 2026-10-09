import ShielddSecurity.Compiler

set_option maxHeartbeats 300000
set_option maxRecDepth 4096
namespace ShielddSecurity.CompilerIndexed01
open Compiler

deriving instance DecidableEq for SourceNode

def checkRowAt (p : Nat) (rows : Array Row) (index : Nat) (expected : Row) : Bool :=
  match rows[index]? with
  | none => false
  | some actual => decide (canonical p actual.a = canonical p expected.a ∧
      canonical p actual.b = canonical p expected.b)

theorem checkRowAt_sound (p : Nat) (rows : Array Row) (index : Nat) (expected : Row)
    (checked : checkRowAt p rows index expected = true) : checkRow p rows.toList expected = true := by
  cases found : rows[index]? with
  | none => simp [checkRowAt,found] at checked
  | some actual =>
      have member : actual ∈ rows.toList := List.mem_of_getElem? (by simpa using found)
      apply List.any_eq_true.mpr
      exact ⟨actual,member,by simpa [checkRowAt,found] using checked⟩

def checkUnoutlinedAt (p copy : Nat) (rows : Array Row) (index : Nat) (expected : Row) : Bool :=
  match rows[index]? with
  | none => false
  | some actual => decide (canonical p (unoutline copy actual.a) = canonical p expected.a ∧
      canonical p (unoutline copy actual.b) = canonical p expected.b)

theorem checkUnoutlinedAt_sound (p copy : Nat) (rows : Array Row) (index : Nat) (expected : Row)
    (checked : checkUnoutlinedAt p copy rows index expected = true) :
    checkRow p (unoutlineRows copy rows.toList) expected = true := by
  cases found : rows[index]? with
  | none => simp [checkUnoutlinedAt,found] at checked
  | some actual =>
      have member : actual ∈ rows.toList := List.mem_of_getElem? (by simpa using found)
      apply List.any_eq_true.mpr
      refine ⟨⟨unoutline copy actual.a,unoutline copy actual.b⟩,?_,?_⟩
      · exact List.mem_map.mpr ⟨actual,member,rfl⟩
      · simpa [checkUnoutlinedAt,found] using checked

inductive Hint (n : Nat) where
  | constant (coefficient : Int) (output : Linear)
  | input (index : Nat) (output : Linear)
  | add (left right : Fin n) (x y output : Linear)
  | foldedLeft (left right : Fin n) (x y output : Linear) (coefficient : Int)
  | foldedRight (left right : Fin n) (x y output : Linear) (coefficient : Int)
  | deferred (left right : Fin n) (x y base : Linear)
  | square (left right : Fin n) (x y output : Linear) (row : Nat)
  | product (left right : Fin n) (x y output auxiliary : Linear) (minus plus : Nat)

def Hint.node {n : Nat} : Hint n → SourceNode n
  | .constant coefficient _ => .constant coefficient
  | .input index _ => .input index
  | .add left right .. => .add left right
  | .foldedLeft left right .. | .foldedRight left right .. |
    .deferred left right .. | .square left right .. | .product left right .. => .mul left right

def Hint.output {n : Nat} : Hint n → Expression
  | .constant _ output | .input _ output | .add _ _ _ _ output |
    .foldedLeft _ _ _ _ output _ | .foldedRight _ _ _ _ output _ |
    .square _ _ _ _ output _ | .product _ _ _ _ output _ _ _ => .linear output
  | .deferred _ _ _ _ base => .square base

def checkNode {n : Nat} (p copy : Nat) (rows : Array Row) (inputTerms : Nat → Linear)
    (earlier : Fin n → Expression) : Hint n → Bool
  | .constant coefficient output => decide (canonical p output = canonical p [(0,coefficient)])
  | .input index output => decide (canonical p output = canonical p (inputTerms index))
  | .add left right x y output => decide (earlier left = .linear x ∧ earlier right = .linear y ∧
      canonical p output = canonical p (x ++ y))
  | .foldedLeft left right x y output coefficient => decide (earlier left = .linear x ∧
      earlier right = .linear y ∧ canonical p x = canonical p [(0,coefficient)] ∧
      canonical p output = canonical p (scaleLinear coefficient y))
  | .foldedRight left right x y output coefficient => decide (earlier left = .linear x ∧
      earlier right = .linear y ∧ canonical p y = canonical p [(0,coefficient)] ∧
      canonical p output = canonical p (scaleLinear coefficient x))
  | .deferred left right x y base => decide (earlier left = .linear x ∧ earlier right = .linear y ∧
      canonical p base = canonical p x ∧ canonical p base = canonical p y)
  | .square left right x y output row =>
      decide (earlier left = .linear x ∧ earlier right = .linear y ∧ canonical p x = canonical p y) &&
      checkUnoutlinedAt p copy rows row ⟨x,output⟩
  | .product left right x y output auxiliary minus plus =>
      decide (earlier left = .linear x ∧ earlier right = .linear y) &&
      checkUnoutlinedAt p copy rows minus ⟨subtract x y,auxiliary⟩ &&
      checkUnoutlinedAt p copy rows plus ⟨x ++ y,auxiliary ++ scaleLinear 4 output⟩

theorem checkNode_sound {n : Nat} (p copy : Nat) (rows : Array Row) (inputTerms : Nat → Linear)
    (earlier : Fin n → Expression) (hint : Hint n)
    (checked : checkNode p copy rows inputTerms earlier hint = true) :
    NodeCertificate p (unoutlineRows copy rows.toList) inputTerms earlier hint.node hint.output := by
  cases hint with
  | constant coefficient output => exact .constant coefficient output (of_decide_eq_true checked)
  | input index output => exact .input index output (of_decide_eq_true checked)
  | add left right x y output =>
      have h := of_decide_eq_true checked
      exact .add left right x y output h.1 h.2.1 h.2.2
  | foldedLeft left right x y output coefficient =>
      have h := of_decide_eq_true checked
      exact .foldedLeft left right x y output coefficient h.1 h.2.1 h.2.2.1 h.2.2.2
  | foldedRight left right x y output coefficient =>
      have h := of_decide_eq_true checked
      exact .foldedRight left right x y output coefficient h.1 h.2.1 h.2.2.1 h.2.2.2
  | deferred left right x y base =>
      have h := of_decide_eq_true checked
      exact .deferred left right x y base h.1 h.2.1 h.2.2.1 h.2.2.2
  | square left right x y output row =>
      simp only [checkNode,Bool.and_eq_true] at checked
      have h := of_decide_eq_true checked.1
      exact .square left right x y output h.1 h.2.1 h.2.2
        (checkUnoutlinedAt_sound p copy rows row _ checked.2)
  | product left right x y output auxiliary minus plus =>
      simp only [checkNode,Bool.and_eq_true] at checked
      have h := of_decide_eq_true checked.1.1
      exact .product left right x y output auxiliary h.1 h.2
        (checkUnoutlinedAt_sound p copy rows minus _ checked.1.2)
        (checkUnoutlinedAt_sound p copy rows plus _ checked.2)

def checkBlock {inputs nodes : Nat} (p copy : Nat) (rows : Array Row)
    (inputTerms : Nat → Linear) (graph : SourceGraph inputs nodes)
    (expressions : Fin nodes → Expression) (hints : (index : Fin nodes) → Hint index.val)
    (indices : List (Fin nodes)) : Bool :=
  indices.all (fun index => decide ((hints index).node = graph.node index ∧
    (hints index).output = expressions index) &&
    checkNode p copy rows inputTerms (graph.prior expressions index) (hints index))

theorem checkBlock_sound {inputs nodes : Nat} (p copy : Nat) (rows : Array Row)
    (inputTerms : Nat → Linear) (graph : SourceGraph inputs nodes)
    (expressions : Fin nodes → Expression) (hints : (index : Fin nodes) → Hint index.val)
    (indices : List (Fin nodes)) (checked : checkBlock p copy rows inputTerms graph expressions hints indices = true)
    (index : Fin nodes) (member : index ∈ indices) :
    NodeCertificate p (unoutlineRows copy rows.toList) inputTerms
      (graph.prior expressions index) (graph.node index) (expressions index) := by
  have h := List.all_eq_true.mp checked index member
  simp only [Bool.and_eq_true] at h
  have identity := of_decide_eq_true h.1
  have result := checkNode_sound p copy rows inputTerms (graph.prior expressions index) (hints index) h.2
  simpa only [identity.1,identity.2] using result

end ShielddSecurity.CompilerIndexed01
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexed01.checkRowAt_sound
#print axioms ShielddSecurity.CompilerIndexed01.checkRowAt_sound
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexed01.checkUnoutlinedAt_sound
#print axioms ShielddSecurity.CompilerIndexed01.checkUnoutlinedAt_sound
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexed01.checkNode_sound
#print axioms ShielddSecurity.CompilerIndexed01.checkNode_sound
set_option pp.all true in
#check @ShielddSecurity.CompilerIndexed01.checkBlock_sound
#print axioms ShielddSecurity.CompilerIndexed01.checkBlock_sound
