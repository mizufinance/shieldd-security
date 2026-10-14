-- GENERATED from rows.json. Do not hand edit.
import ShielddSecurity.VariableOperationAdapter434
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.DetectionSelector626
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
def xRows : List Row := [⟨[(10,1),(14,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33791,1)]⟩,⟨[(10,1),(14,1),(200692,34603644889727414955607589073122773917057272212473650571642302237253952351023)],[(33790,4),(33791,1)]⟩]
theorem x_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 11052 2 xRows=true := by decide +kernel
theorem x_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 33790=rho 10*(rho 14-(17832230285398775523840151435063191920633280288053987250961356462684628833490:F)*rho copy) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 11052 2 xRows x_checked (by decide) rho arithmetic
  have result := checked_product_sound rho xRows [(10,1)] [(14,1),(copy,-17832230285398775523840151435063191920633280288053987250961356462684628833490)]
    [(33790,1)] [(33791,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero,Int.cast_neg,Int.cast_ofNat,neg_mul,sub_eq_add_neg] using result
def yRows : List Row := [⟨[(10,1),(15,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,52236742954115892447572473178524297982305297140137344394933767595493156073169)],[(33793,1)]⟩,⟨[(10,1),(15,1),(200692,199132221010298031875267329661667855385255360390293427669891104445425111344)],[(33792,4),(33793,1)]⟩]
theorem y_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 11054 2 yRows=true := by decide +kernel
theorem y_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 33792=rho 10*(rho 15-(52236742954115892447572473178524297982305297140137344394933767595493156073169:F)*rho copy) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 11054 2 yRows y_checked (by decide) rho arithmetic
  have result := checked_product_sound rho yRows [(10,1)] [(15,1),(copy,-52236742954115892447572473178524297982305297140137344394933767595493156073169)]
    [(33792,1)] [(33793,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero,Int.cast_neg,Int.cast_ofNat,neg_mul,sub_eq_add_neg] using result
end ShielddSecurity.DetectionSelector626
set_option pp.all true in
#check @ShielddSecurity.DetectionSelector626.x_checked
#print axioms ShielddSecurity.DetectionSelector626.x_checked
set_option pp.all true in
#check @ShielddSecurity.DetectionSelector626.x_value
#print axioms ShielddSecurity.DetectionSelector626.x_value
set_option pp.all true in
#check @ShielddSecurity.DetectionSelector626.y_checked
#print axioms ShielddSecurity.DetectionSelector626.y_checked
set_option pp.all true in
#check @ShielddSecurity.DetectionSelector626.y_value
#print axioms ShielddSecurity.DetectionSelector626.y_value
