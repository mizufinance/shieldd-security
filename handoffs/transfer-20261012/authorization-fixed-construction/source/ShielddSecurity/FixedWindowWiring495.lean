import ShielddSecurity.FixedWindowJoin488
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedWindowWiring495
open Compiler CompilerArithmeticTransport41
def Shape (e : FixedWindowJoin488.Entry) : Prop :=
  e.operation.isAdd=true ∧ 1≤e.index ∧ e.index<126 ∧
  VariableOperationAdapter434.port e.operation 1=[(4017+2*e.index,1)] ∧
  VariableOperationAdapter434.port e.operation 2=[(4018+2*e.index,1)] ∧
  canonical p (VariableOperationAdapter434.port e.operation 3)=canonical p e.selector.outputX ∧
  canonical p (VariableOperationAdapter434.port e.operation 4)=canonical p e.selector.outputY ∧
  VariableOperationAdapter434.port e.operation 5=[(4019+2*e.index,1)] ∧
  VariableOperationAdapter434.port e.operation 6=[(4020+2*e.index,1)] ∧
  e.selector.low=3767+2*e.index ∧ e.selector.high=3768+2*e.index ∧
  e.operation.assertionStart=4028+2*e.index

noncomputable instance shapeDecidable (e : FixedWindowJoin488.Entry) : Decidable (Shape e) := by
  unfold Shape
  infer_instance
noncomputable def check (e : FixedWindowJoin488.Entry) : Bool := decide (Shape e)
theorem checked (e : FixedWindowJoin488.Entry)
    (operation : VariableOperationAdapter434.check e.operation=true)
    (selector : FixedSelectorAdapter480.check e.selector=true) (shape : check e=true) :
    FixedWindowJoin488.check e=true := by
  have valid : FixedWindowJoin488.Valid e := ⟨operation,selector,of_decide_eq_true shape⟩
  simp only [FixedWindowJoin488.check,valid,decide_true]
end ShielddSecurity.FixedWindowWiring495

set_option pp.all true in
#check @ShielddSecurity.FixedWindowWiring495.Shape
#print axioms ShielddSecurity.FixedWindowWiring495.Shape

set_option pp.all true in
#check @ShielddSecurity.FixedWindowWiring495.check
#print axioms ShielddSecurity.FixedWindowWiring495.check

set_option pp.all true in
#check @ShielddSecurity.FixedWindowWiring495.checked
#print axioms ShielddSecurity.FixedWindowWiring495.checked
