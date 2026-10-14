-- GENERATED from rows.json. Do not hand edit.
import ShielddSecurity.VariableOperationAdapter434
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CheckingSelector597
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
def xRows : List Row := [⟨[(10,1),(42,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121571,1)]⟩,⟨[(10,1),(42,1),(200692,2613035198500699080012737903016384954916552590968062488514021062113153911183)],[(121570,4),(121571,1)]⟩]
theorem x_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 98832 2 xRows=true := by decide +kernel
theorem x_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 121570=rho 10*(rho 42-(49822839976625491399435002605169580882773999909559575334089637637825427273330:F)*rho copy) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 98832 2 xRows x_checked (by decide) rho arithmetic
  have result := checked_product_sound rho xRows [(10,1)] [(42,1),(copy,-49822839976625491399435002605169580882773999909559575334089637637825427273330)]
    [(121570,1)] [(121571,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero,Int.cast_neg,Int.cast_ofNat,neg_mul,sub_eq_add_neg] using result
def yRows : List Row := [⟨[(10,1),(43,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],[(121573,1)]⟩,⟨[(10,1),(43,1),(200692,23326889571876200994796012627856472314977644248009733575144307806885254871463)],[(121572,4),(121573,1)]⟩]
theorem y_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 98834 2 yRows=true := by decide +kernel
theorem y_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 121572=rho 10*(rho 43-(29108985603249989484651727880329493522712908252517904247459350893053326313050:F)*rho copy) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 98834 2 yRows y_checked (by decide) rho arithmetic
  have result := checked_product_sound rho yRows [(10,1)] [(43,1),(copy,-29108985603249989484651727880329493522712908252517904247459350893053326313050)]
    [(121572,1)] [(121573,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero,Int.cast_neg,Int.cast_ofNat,neg_mul,sub_eq_add_neg] using result
end ShielddSecurity.CheckingSelector597
set_option pp.all true in
#check @ShielddSecurity.CheckingSelector597.x_checked
#print axioms ShielddSecurity.CheckingSelector597.x_checked
set_option pp.all true in
#check @ShielddSecurity.CheckingSelector597.x_value
#print axioms ShielddSecurity.CheckingSelector597.x_value
set_option pp.all true in
#check @ShielddSecurity.CheckingSelector597.y_checked
#print axioms ShielddSecurity.CheckingSelector597.y_checked
set_option pp.all true in
#check @ShielddSecurity.CheckingSelector597.y_value
#print axioms ShielddSecurity.CheckingSelector597.y_value
