import ShielddSecurity.VariableSelectorAdapter437
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableWindowJoin443
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
abbrev Op := VariableOperationAdapter434.Entry
abbrev Selector := VariableSelectorAdapter437.Entry
structure Entry where
  first : Op
  second : Op
  addition : Op
  selector : Selector

def same (left right : Linear) : Prop := canonical p left=canonical p right
noncomputable instance sameDecidable (left right : Linear) : Decidable (same left right) := by
  unfold same;infer_instance

def Valid (e : Entry) : Prop :=
  e.first.isAdd=false ∧ e.second.isAdd=false ∧ e.addition.isAdd=true ∧
  same (VariableOperationAdapter434.port e.first 3) (VariableOperationAdapter434.port e.second 1) ∧
  same (VariableOperationAdapter434.port e.first 4) (VariableOperationAdapter434.port e.second 2) ∧
  same (VariableOperationAdapter434.port e.second 3) (VariableOperationAdapter434.port e.addition 1) ∧
  same (VariableOperationAdapter434.port e.second 4) (VariableOperationAdapter434.port e.addition 2) ∧
  same e.selector.outputX (VariableOperationAdapter434.port e.addition 3) ∧
  same e.selector.outputY (VariableOperationAdapter434.port e.addition 4)
noncomputable instance validDecidable (e : Entry) : Decidable (Valid e) := by
  unfold Valid;infer_instance
noncomputable def check (e : Entry) : Bool := decide (Valid e)

def point {F : Type} [Field F] (rho : Nat → F) (x y : Linear) : Group.Point F := ⟨eval rho x,eval rho y⟩
def opPoint {F : Type} [Field F] (rho : Nat → F) (e : Op) (x : Nat) : Group.Point F :=
  point rho (VariableOperationAdapter434.port e x) (VariableOperationAdapter434.port e (x+1))
def selectorPoint {F : Type} [Field F] (rho : Nat → F) (e : Selector) (x : Nat) : Group.Point F :=
  point rho (VariableSelectorAdapter437.port e x) (VariableSelectorAdapter437.port e (x+1))
def witness {F : Type} [Field F] (rho : Nat → F) (e : Entry) (low high : Bool) : TransferOwnership.WindowWitness F :=
  ⟨low,high,opPoint rho e.first 3,opPoint rho e.second 3,opPoint rho e.addition 5⟩
def Rows {F : Type} [Field F] (rho : Nat → F) (e : Entry) : Prop :=
  VariableOperationAdapter434.Rows rho e.first ∧ VariableOperationAdapter434.Rows rho e.second ∧
  VariableOperationAdapter434.Rows rho e.addition
variable {F : Type} [Field F] [CharP F p]
theorem point_equal (rho : Nat → F) (lx ly rx ry : Linear)
    (x : same lx rx) (y : same ly ry) : point rho lx ly=point rho rx ry := by
  unfold point
  rw [canonical_equal rho lx rx x,canonical_equal rho ly ry y]

theorem equations_iff (e : Entry) (checked : check e=true)
    (first : VariableOperationAdapter434.check e.first=true)
    (second : VariableOperationAdapter434.check e.second=true)
    (addition : VariableOperationAdapter434.check e.addition=true)
    (selector : VariableSelectorAdapter437.check e.selector=true) (rho : Nat → F)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (low high : Bool)
    (lowBit : eval rho (VariableSelectorAdapter437.port e.selector 1)=(if low then 1 else 0))
    (highBit : eval rho (VariableSelectorAdapter437.port e.selector 2)=(if high then 1 else 0)) :
    Rows rho e ↔ TransferOwnership.WindowEquations (CapturedFirstSubgroup81.d:F)
      (selectorPoint rho e.selector 3) (selectorPoint rho e.selector 5) (selectorPoint rho e.selector 7)
      (opPoint rho e.first 1) (witness rho e low high) := by
  have valid : Valid e := of_decide_eq_true checked
  rcases valid with ⟨fkind,skind,akind,fX,fY,sX,sY,aX,aY⟩
  have firstJoin := point_equal rho _ _ _ _ fX fY
  have secondJoin := point_equal rho _ _ _ _ sX sY
  have selectorJoin := point_equal rho _ _ _ _ aX aY
  have selection := VariableSelectorAdapter437.coordinates e.selector selector rho one arithmetic
  rw [lowBit,highBit] at selection
  unfold Rows
  rw [VariableOperationAdapter434.equations_iff e.first first rho one arithmetic,
    VariableOperationAdapter434.equations_iff e.second second rho one arithmetic,
    VariableOperationAdapter434.equations_iff e.addition addition rho one arithmetic]
  simp only [VariableOperationAdapter434.Equations,fkind,skind,akind,Bool.false_eq_true,if_false,if_true]
  change TransferOwnership.DoubleEquations (opPoint rho e.first 1) (opPoint rho e.first 3) ∧
      TransferOwnership.DoubleEquations (opPoint rho e.second 1) (opPoint rho e.second 3) ∧
      TransferOwnership.AddEquations (CapturedFirstSubgroup81.d:F) (opPoint rho e.addition 1)
        (opPoint rho e.addition 3) (opPoint rho e.addition 5) ↔ _
  change opPoint rho e.first 3=opPoint rho e.second 1 at firstJoin
  change opPoint rho e.second 3=opPoint rho e.addition 1 at secondJoin
  change point rho e.selector.outputX e.selector.outputY=opPoint rho e.addition 3 at selectorJoin
  change point rho e.selector.outputX e.selector.outputY=_ at selection
  rw [←firstJoin,←secondJoin,←selectorJoin,selection]
  rfl
end ShielddSecurity.VariableWindowJoin443

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.Op
#print axioms ShielddSecurity.VariableWindowJoin443.Op

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.Selector
#print axioms ShielddSecurity.VariableWindowJoin443.Selector

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.Entry
#print axioms ShielddSecurity.VariableWindowJoin443.Entry

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.same
#print axioms ShielddSecurity.VariableWindowJoin443.same

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.sameDecidable
#print axioms ShielddSecurity.VariableWindowJoin443.sameDecidable

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.Valid
#print axioms ShielddSecurity.VariableWindowJoin443.Valid

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.validDecidable
#print axioms ShielddSecurity.VariableWindowJoin443.validDecidable

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.check
#print axioms ShielddSecurity.VariableWindowJoin443.check

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.point
#print axioms ShielddSecurity.VariableWindowJoin443.point

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.opPoint
#print axioms ShielddSecurity.VariableWindowJoin443.opPoint

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.selectorPoint
#print axioms ShielddSecurity.VariableWindowJoin443.selectorPoint

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.witness
#print axioms ShielddSecurity.VariableWindowJoin443.witness

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.Rows
#print axioms ShielddSecurity.VariableWindowJoin443.Rows

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.point_equal
#print axioms ShielddSecurity.VariableWindowJoin443.point_equal

set_option pp.all true in
#check @ShielddSecurity.VariableWindowJoin443.equations_iff
#print axioms ShielddSecurity.VariableWindowJoin443.equations_iff
