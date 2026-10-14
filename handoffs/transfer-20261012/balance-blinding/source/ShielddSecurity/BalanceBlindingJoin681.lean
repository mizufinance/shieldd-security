import ShielddSecurity.BalanceBlindingMeaning674
import ShielddSecurity.VariableWindowColumns449
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingJoin681
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableWindowColumns449
abbrev Entry := FixedWindowJoin488.Entry
structure Layout where
  bits : Nat
  points : Nat
  assertions : Nat

def Valid (layout : Layout) (e : Entry) : Prop :=
  VariableOperationAdapter434.check e.operation=true ∧ FixedSelectorAdapter480.check e.selector=true ∧
  e.operation.isAdd=true ∧ 1≤e.index ∧ e.index<126 ∧
  VariableOperationAdapter434.port e.operation 1=[(layout.points+2*(e.index-1),1)] ∧
  VariableOperationAdapter434.port e.operation 2=[(layout.points+2*(e.index-1)+1,1)] ∧
  canonical p (VariableOperationAdapter434.port e.operation 3)=canonical p e.selector.outputX ∧
  canonical p (VariableOperationAdapter434.port e.operation 4)=canonical p e.selector.outputY ∧
  VariableOperationAdapter434.port e.operation 5=[(layout.points+2*e.index,1)] ∧
  VariableOperationAdapter434.port e.operation 6=[(layout.points+2*e.index+1,1)] ∧
  e.selector.low=layout.bits+2*e.index ∧ e.selector.high=layout.bits+2*e.index+1 ∧
  e.operation.assertionStart=layout.assertions+2*(e.index-1)
noncomputable instance validDecidable (layout : Layout) (e : Entry) : Decidable (Valid layout e) := by unfold Valid;infer_instance
noncomputable def check (layout : Layout) (e : Entry) : Bool := decide (Valid layout e)
variable {F : Type} [Field F] [CharP F p]

theorem rows_iff (layout : Layout) (e : Entry) (checked : check layout e=true) (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    VariableOperationAdapter434.Rows rho e.operation ↔
      TransferOwnership.AddEquations (CapturedFirstSubgroup81.d:F)
        (columnPoint rho (layout.points+2*(e.index-1)))
        (Group.windowPoint (rho (layout.bits+2*e.index)) (rho (layout.bits+2*e.index+1))
          (FixedSelectorAdapter480.base e.selector) (FixedSelectorAdapter480.twice e.selector)
          (FixedSelectorAdapter480.triple e.selector))
        (columnPoint rho (layout.points+2*e.index)) := by
  have valid : Valid layout e := of_decide_eq_true checked
  rcases valid with ⟨op,sel,kind,lower,upper,lx,ly,rx,ry,ox,oy,low,high,position⟩
  have right := FixedSelectorAdapter480.coordinates e.selector sel rho one arithmetic
  rw [←canonical_equal rho (VariableOperationAdapter434.port e.operation 3) e.selector.outputX rx,
    ←canonical_equal rho (VariableOperationAdapter434.port e.operation 4) e.selector.outputY ry,low,high] at right
  rw [VariableOperationAdapter434.equations_iff e.operation op rho one arithmetic,
    VariableOperationAdapter434.Equations,kind]
  simp only [if_true]
  rw [right,lx,ly,ox,oy]
  simp only [eval,Int.cast_one,one_mul,add_zero,columnPoint]
open ConcreteJubjubField01
theorem complete (layout : Layout) (e : Entry) (checked : check layout e=true)
    (matched : BalanceBlindingMeaning674.check e=true) (rho : Nat → ConcreteJubjubField01.F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (low high : Bool) (previous output : Group.Point ConcreteJubjubField01.F)
    (lowMeaning : rho (layout.bits+2*e.index)=if low then 1 else 0)
    (highMeaning : rho (layout.bits+2*e.index+1)=if high then 1 else 0)
    (previousMeaning : columnPoint rho (layout.points+2*(e.index-1))=previous)
    (outputMeaning : columnPoint rho (layout.points+2*e.index)=output)
    (equations : TransferOwnership.AddEquations (CapturedFirstSubgroup81.d:ConcreteJubjubField01.F) previous
      (Group.windowPoint (if low then 1 else 0) (if high then 1 else 0)
        (FixedSelectorAdapter480.base (BalanceBlindingTables673.table e.index).1)
        (FixedSelectorAdapter480.twice (BalanceBlindingTables673.table e.index).1)
        (FixedSelectorAdapter480.triple (BalanceBlindingTables673.table e.index).1)) output) :
    VariableOperationAdapter434.Rows rho e.operation := by
  apply (rows_iff layout e checked rho one arithmetic).mpr
  have points := BalanceBlindingMeaning674.points e matched
  rw [lowMeaning,highMeaning,previousMeaning,outputMeaning,points.1,points.2.1,points.2.2]
  exact equations
end ShielddSecurity.BalanceBlindingJoin681

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingJoin681.Entry
#print axioms ShielddSecurity.BalanceBlindingJoin681.Entry

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingJoin681.Valid
#print axioms ShielddSecurity.BalanceBlindingJoin681.Valid

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingJoin681.check
#print axioms ShielddSecurity.BalanceBlindingJoin681.check

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingJoin681.rows_iff
#print axioms ShielddSecurity.BalanceBlindingJoin681.rows_iff

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingJoin681.complete
#print axioms ShielddSecurity.BalanceBlindingJoin681.complete
