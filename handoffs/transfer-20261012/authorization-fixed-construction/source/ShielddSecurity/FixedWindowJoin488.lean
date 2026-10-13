import ShielddSecurity.FixedSelectorAdapter480
import ShielddSecurity.VariableWindowColumns449
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedWindowJoin488
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableWindowColumns449
structure Entry where
  index : Nat
  operation : VariableOperationAdapter434.Entry
  selector : FixedSelectorAdapter480.Entry

def Valid (e : Entry) : Prop :=
  VariableOperationAdapter434.check e.operation=true ∧ FixedSelectorAdapter480.check e.selector=true ∧
  e.operation.isAdd=true ∧ 1≤e.index ∧ e.index<126 ∧
  VariableOperationAdapter434.port e.operation 1=[(4017+2*e.index,1)] ∧
  VariableOperationAdapter434.port e.operation 2=[(4018+2*e.index,1)] ∧
  canonical p (VariableOperationAdapter434.port e.operation 3)=canonical p e.selector.outputX ∧
  canonical p (VariableOperationAdapter434.port e.operation 4)=canonical p e.selector.outputY ∧
  VariableOperationAdapter434.port e.operation 5=[(4019+2*e.index,1)] ∧
  VariableOperationAdapter434.port e.operation 6=[(4020+2*e.index,1)] ∧
  e.selector.low=3767+2*e.index ∧ e.selector.high=3768+2*e.index ∧
  e.operation.assertionStart=4028+2*e.index
noncomputable instance validDecidable (e : Entry) : Decidable (Valid e) := by unfold Valid;infer_instance
noncomputable def check (e : Entry) : Bool := decide (Valid e)
variable {F : Type} [Field F] [CharP F p]

theorem rows_iff (e : Entry) (checked : check e=true) (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    VariableOperationAdapter434.Rows rho e.operation ↔
      TransferOwnership.AddEquations (CapturedFirstSubgroup81.d:F)
        (columnPoint rho (4017+2*e.index))
        (Group.windowPoint (rho (3767+2*e.index)) (rho (3768+2*e.index))
          (FixedSelectorAdapter480.base e.selector) (FixedSelectorAdapter480.twice e.selector)
          (FixedSelectorAdapter480.triple e.selector))
        (columnPoint rho (4019+2*e.index)) := by
  have valid : Valid e := of_decide_eq_true checked
  rcases valid with ⟨op,sel,kind,lower,upper,lx,ly,rx,ry,ox,oy,low,high,position⟩
  have right := FixedSelectorAdapter480.coordinates e.selector sel rho one arithmetic
  rw [←canonical_equal rho (VariableOperationAdapter434.port e.operation 3) e.selector.outputX rx,
    ←canonical_equal rho (VariableOperationAdapter434.port e.operation 4) e.selector.outputY ry,low,high] at right
  rw [VariableOperationAdapter434.equations_iff e.operation op rho one arithmetic,
    VariableOperationAdapter434.Equations,kind]
  simp only [if_true]
  rw [right,lx,ly,ox,oy]
  simp only [eval,Int.cast_one,one_mul,add_zero,columnPoint]
  have leftIndex : 4017+2*e.index+1=4018+2*e.index := by omega
  have outIndex : 4019+2*e.index+1=4020+2*e.index := by omega
  rw [leftIndex,outIndex]
end ShielddSecurity.FixedWindowJoin488

set_option pp.all true in
#check @ShielddSecurity.FixedWindowJoin488.Entry
#print axioms ShielddSecurity.FixedWindowJoin488.Entry

set_option pp.all true in
#check @ShielddSecurity.FixedWindowJoin488.Valid
#print axioms ShielddSecurity.FixedWindowJoin488.Valid

set_option pp.all true in
#check @ShielddSecurity.FixedWindowJoin488.check
#print axioms ShielddSecurity.FixedWindowJoin488.check

set_option pp.all true in
#check @ShielddSecurity.FixedWindowJoin488.rows_iff
#print axioms ShielddSecurity.FixedWindowJoin488.rows_iff
