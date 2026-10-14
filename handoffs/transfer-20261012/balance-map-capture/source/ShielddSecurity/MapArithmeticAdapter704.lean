import ShielddSecurity.FixedSelectorAdapter480
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapArithmeticAdapter704
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
structure Entry where
  sourceNode : Nat
  square : Bool
  left : Linear
  right : Linear
  output : Linear
  auxiliary : Linear
  start : Nat
  rows : List Row

def Shape (e : Entry) : Prop :=
  if e.square then checkRow p e.rows ⟨e.left,e.output⟩=true else
    checkRow p e.rows ⟨subtract e.left e.right,e.auxiliary⟩=true ∧
    checkRow p e.rows ⟨e.left++e.right,e.auxiliary++scaleLinear 4 e.output⟩=true
noncomputable instance shapeDecidable (e : Entry) : Decidable (Shape e) := by
  unfold Shape
  infer_instance
noncomputable def check (e : Entry) : Bool :=
  CompilerRowSlice63.check CapturedFullArithmetic52.rowAt e.start e.rows.length e.rows &&
  decide (e.start+e.rows.length≤177954) && decide (Shape e)

variable {F : Type} [Field F] [CharP F p]
theorem equation (e : Entry) (checked : check e=true) (rho : Nat → F)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    eval rho e.output=if e.square then eval rho e.left*eval rho e.left else eval rho e.left*eval rho e.right := by
  have checks := Bool.and_eq_true_iff.mp checked
  have bounds := Bool.and_eq_true_iff.mp checks.1
  have shape : Shape e := of_decide_eq_true checks.2
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954
    e.start e.rows.length e.rows bounds.1 (of_decide_eq_true bounds.2) rho arithmetic
  cases h : e.square
  · simp only [Shape,h,Bool.false_eq_true,if_false] at shape ⊢
    exact checked_product_sound rho e.rows e.left e.right e.output e.auxiliary four_ne_zero sat shape.1 shape.2
  · simp only [Shape,h,if_true] at shape ⊢
    exact checked_square_sound rho e.rows e.left e.output sat shape
end ShielddSecurity.MapArithmeticAdapter704

set_option pp.all true in
#check @ShielddSecurity.MapArithmeticAdapter704.equation
#print axioms ShielddSecurity.MapArithmeticAdapter704.equation
