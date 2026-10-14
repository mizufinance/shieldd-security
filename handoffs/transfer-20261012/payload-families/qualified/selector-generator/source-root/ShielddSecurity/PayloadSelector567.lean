import ShielddSecurity.VariableOperationAdapter434
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PayloadSelector567
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
def xRows : List Row := [⟨[(10,1),(35,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(87779,1)]⟩,⟨[(10,1),(35,1),(200692,2613035198500699080012737903016384954916552590968062488514021062113153911183)],[(87778,4),(87779,1)]⟩]
theorem x_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 65040 2 xRows=true := by decide +kernel
theorem x_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 87778=rho 10*(rho 35-(49822839976625491399435002605169580882773999909559575334089637637825427273330:F)*rho copy) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 65040 2 xRows x_checked (by decide) rho arithmetic
  have result := checked_product_sound rho xRows [(10,1)] [(35,1),(copy,-49822839976625491399435002605169580882773999909559575334089637637825427273330)]
    [(87778,1)] [(87779,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero,Int.cast_neg,Int.cast_ofNat,neg_mul,sub_eq_add_neg] using result
def yRows : List Row := [⟨[(10,1),(36,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],[(87781,1)]⟩,⟨[(10,1),(36,1),(200692,23326889571876200994796012627856472314977644248009733575144307806885254871463)],[(87780,4),(87781,1)]⟩]
theorem y_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 65042 2 yRows=true := by decide +kernel
theorem y_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 87780=rho 10*(rho 36-(29108985603249989484651727880329493522712908252517904247459350893053326313050:F)*rho copy) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 65042 2 yRows y_checked (by decide) rho arithmetic
  have result := checked_product_sound rho yRows [(10,1)] [(36,1),(copy,-29108985603249989484651727880329493522712908252517904247459350893053326313050)]
    [(87780,1)] [(87781,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero,Int.cast_neg,Int.cast_ofNat,neg_mul,sub_eq_add_neg] using result
end ShielddSecurity.PayloadSelector567
set_option pp.all true in
#check @ShielddSecurity.PayloadSelector567.x_checked
#print axioms ShielddSecurity.PayloadSelector567.x_checked
set_option pp.all true in
#check @ShielddSecurity.PayloadSelector567.x_value
#print axioms ShielddSecurity.PayloadSelector567.x_value
set_option pp.all true in
#check @ShielddSecurity.PayloadSelector567.y_checked
#print axioms ShielddSecurity.PayloadSelector567.y_checked
set_option pp.all true in
#check @ShielddSecurity.PayloadSelector567.y_value
#print axioms ShielddSecurity.PayloadSelector567.y_value
