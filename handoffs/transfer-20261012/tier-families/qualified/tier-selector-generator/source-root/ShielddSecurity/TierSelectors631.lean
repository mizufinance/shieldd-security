-- GENERATED from rows.json. Do not hand edit.
import ShielddSecurity.VariableOperationAdapter434
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TierSelectors631
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
def payloadXRows : List Row := [⟨[(10,1),(35,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,49822839976625491399435002605169580882773999909559575334089637637825427273330)],[(121567,1)]⟩,⟨[(10,1),(35,1),(200692,2613035198500699080012737903016384954916552590968062488514021062113153911183)],[(121566,4),(121567,1)]⟩]
theorem payloadX_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 98828 2 payloadXRows=true := by decide +kernel
theorem payloadX_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 121566=rho 10*eval rho [(35,1),(200692,-49822839976625491399435002605169580882773999909559575334089637637825427273330)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 98828 2 payloadXRows payloadX_checked (by decide) rho arithmetic
  have result := checked_product_sound rho payloadXRows [(10,1)] [(35,1),(200692,-49822839976625491399435002605169580882773999909559575334089637637825427273330)]
    [(121566,1)] [(121567,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
def payloadYRows : List Row := [⟨[(10,1),(36,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],[(121569,1)]⟩,⟨[(10,1),(36,1),(200692,23326889571876200994796012627856472314977644248009733575144307806885254871463)],[(121568,4),(121569,1)]⟩]
theorem payloadY_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 98830 2 payloadYRows=true := by decide +kernel
theorem payloadY_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 121568=rho 10*eval rho [(36,1),(200692,-29108985603249989484651727880329493522712908252517904247459350893053326313050)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 98830 2 payloadYRows payloadY_checked (by decide) rho arithmetic
  have result := checked_product_sound rho payloadYRows [(10,1)] [(36,1),(200692,-29108985603249989484651727880329493522712908252517904247459350893053326313050)]
    [(121568,1)] [(121569,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
def family0XRows : List Row := [⟨[(33790,52435875175126190479447740508185965837690552500527637822603658699938581184512),(108486,1),(121566,1),(200692,31990609691226715875594851170106388962140719621505588083128281175140798439840)],[(142313,1)]⟩,⟨[(33790,1),(108486,1),(121566,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,20445265483899474603852889338079576875549832879022049739475377524797782744673)],[(142312,4),(142313,1)]⟩]
theorem family0X_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 119574 2 family0XRows=true := by decide +kernel
theorem family0X_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 142312=rho 108486*eval rho [(33790,1),(121566,-1),(200692,(17832230285398775523840151435063191920633280288053987250961356462684628833490:Int)-49822839976625491399435002605169580882773999909559575334089637637825427273330)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 119574 2 family0XRows family0X_checked (by decide) rho arithmetic
  have result := checked_product_sound rho family0XRows [(108486,1)] [(33790,1),(121566,-1),(200692,(17832230285398775523840151435063191920633280288053987250961356462684628833490:Int)-49822839976625491399435002605169580882773999909559575334089637637825427273330)]
    [(142312,1)] [(142313,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
def family0YRows : List Row := [⟨[(33792,52435875175126190479447740508185965837690552500527637822603658699938581184512),(108486,1),(121568,1),(200692,29308117824260287516526995209991161378098163612908197675129241997498751424394)],[(142315,1)]⟩,⟨[(33792,1),(108486,1),(121568,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,23127757350865902962920745298194804459592388887619440147474416702439829760119)],[(142314,4),(142315,1)]⟩]
theorem family0Y_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 119576 2 family0YRows=true := by decide +kernel
theorem family0Y_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 142314=rho 108486*eval rho [(33792,1),(121568,-1),(200692,(52236742954115892447572473178524297982305297140137344394933767595493156073169:Int)-29108985603249989484651727880329493522712908252517904247459350893053326313050)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 119576 2 family0YRows family0Y_checked (by decide) rho arithmetic
  have result := checked_product_sound rho family0YRows [(108486,1)] [(33792,1),(121568,-1),(200692,(52236742954115892447572473178524297982305297140137344394933767595493156073169:Int)-29108985603249989484651727880329493522712908252517904247459350893053326313050)]
    [(142314,1)] [(142315,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
def family2XRows : List Row := [⟨[(33790,52435875175126190479447740508185965837690552500527637822603658699938581184512),(108486,1),(121566,1),(200692,31990609691226715875594851170106388962140719621505588083128281175140798439840)],[(154387,1)]⟩,⟨[(33790,1),(108486,1),(121566,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,20445265483899474603852889338079576875549832879022049739475377524797782744673)],[(154386,4),(154387,1)]⟩]
theorem family2X_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 131648 2 family2XRows=true := by decide +kernel
theorem family2X_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 154386=rho 108486*eval rho [(33790,1),(121566,-1),(200692,(17832230285398775523840151435063191920633280288053987250961356462684628833490:Int)-49822839976625491399435002605169580882773999909559575334089637637825427273330)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 131648 2 family2XRows family2X_checked (by decide) rho arithmetic
  have result := checked_product_sound rho family2XRows [(108486,1)] [(33790,1),(121566,-1),(200692,(17832230285398775523840151435063191920633280288053987250961356462684628833490:Int)-49822839976625491399435002605169580882773999909559575334089637637825427273330)]
    [(154386,1)] [(154387,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
def family2YRows : List Row := [⟨[(33792,52435875175126190479447740508185965837690552500527637822603658699938581184512),(108486,1),(121568,1),(200692,29308117824260287516526995209991161378098163612908197675129241997498751424394)],[(154389,1)]⟩,⟨[(33792,1),(108486,1),(121568,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,23127757350865902962920745298194804459592388887619440147474416702439829760119)],[(154388,4),(154389,1)]⟩]
theorem family2Y_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 131650 2 family2YRows=true := by decide +kernel
theorem family2Y_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 154388=rho 108486*eval rho [(33792,1),(121568,-1),(200692,(52236742954115892447572473178524297982305297140137344394933767595493156073169:Int)-29108985603249989484651727880329493522712908252517904247459350893053326313050)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 131650 2 family2YRows family2Y_checked (by decide) rho arithmetic
  have result := checked_product_sound rho family2YRows [(108486,1)] [(33792,1),(121568,-1),(200692,(52236742954115892447572473178524297982305297140137344394933767595493156073169:Int)-29108985603249989484651727880329493522712908252517904247459350893053326313050)]
    [(154388,1)] [(154389,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
def family3XRows : List Row := [⟨[(33790,52435875175126190479447740508185965837690552500527637822603658699938581184512),(108486,1),(121566,1),(200692,31990609691226715875594851170106388962140719621505588083128281175140798439840)],[(161680,1)]⟩,⟨[(33790,1),(108486,1),(121566,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,20445265483899474603852889338079576875549832879022049739475377524797782744673)],[(161679,4),(161680,1)]⟩]
theorem family3X_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 138941 2 family3XRows=true := by decide +kernel
theorem family3X_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 161679=rho 108486*eval rho [(33790,1),(121566,-1),(200692,(17832230285398775523840151435063191920633280288053987250961356462684628833490:Int)-49822839976625491399435002605169580882773999909559575334089637637825427273330)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 138941 2 family3XRows family3X_checked (by decide) rho arithmetic
  have result := checked_product_sound rho family3XRows [(108486,1)] [(33790,1),(121566,-1),(200692,(17832230285398775523840151435063191920633280288053987250961356462684628833490:Int)-49822839976625491399435002605169580882773999909559575334089637637825427273330)]
    [(161679,1)] [(161680,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
def family3YRows : List Row := [⟨[(33792,52435875175126190479447740508185965837690552500527637822603658699938581184512),(108486,1),(121568,1),(200692,29308117824260287516526995209991161378098163612908197675129241997498751424394)],[(161682,1)]⟩,⟨[(33792,1),(108486,1),(121568,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,23127757350865902962920745298194804459592388887619440147474416702439829760119)],[(161681,4),(161682,1)]⟩]
theorem family3Y_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 138943 2 family3YRows=true := by decide +kernel
theorem family3Y_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 161681=rho 108486*eval rho [(33792,1),(121568,-1),(200692,(52236742954115892447572473178524297982305297140137344394933767595493156073169:Int)-29108985603249989484651727880329493522712908252517904247459350893053326313050)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 138943 2 family3YRows family3Y_checked (by decide) rho arithmetic
  have result := checked_product_sound rho family3YRows [(108486,1)] [(33792,1),(121568,-1),(200692,(52236742954115892447572473178524297982305297140137344394933767595493156073169:Int)-29108985603249989484651727880329493522712908252517904247459350893053326313050)]
    [(161681,1)] [(161682,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
def family4XRows : List Row := [⟨[(33790,52435875175126190479447740508185965837690552500527637822603658699938581184512),(108486,1),(121566,1),(200692,31990609691226715875594851170106388962140719621505588083128281175140798439840)],[(168973,1)]⟩,⟨[(33790,1),(108486,1),(121566,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,20445265483899474603852889338079576875549832879022049739475377524797782744673)],[(168972,4),(168973,1)]⟩]
theorem family4X_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 146234 2 family4XRows=true := by decide +kernel
theorem family4X_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 168972=rho 108486*eval rho [(33790,1),(121566,-1),(200692,(17832230285398775523840151435063191920633280288053987250961356462684628833490:Int)-49822839976625491399435002605169580882773999909559575334089637637825427273330)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 146234 2 family4XRows family4X_checked (by decide) rho arithmetic
  have result := checked_product_sound rho family4XRows [(108486,1)] [(33790,1),(121566,-1),(200692,(17832230285398775523840151435063191920633280288053987250961356462684628833490:Int)-49822839976625491399435002605169580882773999909559575334089637637825427273330)]
    [(168972,1)] [(168973,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
def family4YRows : List Row := [⟨[(33792,52435875175126190479447740508185965837690552500527637822603658699938581184512),(108486,1),(121568,1),(200692,29308117824260287516526995209991161378098163612908197675129241997498751424394)],[(168975,1)]⟩,⟨[(33792,1),(108486,1),(121568,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,23127757350865902962920745298194804459592388887619440147474416702439829760119)],[(168974,4),(168975,1)]⟩]
theorem family4Y_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 146236 2 family4YRows=true := by decide +kernel
theorem family4Y_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 168974=rho 108486*eval rho [(33792,1),(121568,-1),(200692,(52236742954115892447572473178524297982305297140137344394933767595493156073169:Int)-29108985603249989484651727880329493522712908252517904247459350893053326313050)] := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 146236 2 family4YRows family4Y_checked (by decide) rho arithmetic
  have result := checked_product_sound rho family4YRows [(108486,1)] [(33792,1),(121568,-1),(200692,(52236742954115892447572473178524297982305297140137344394933767595493156073169:Int)-29108985603249989484651727880329493522712908252517904247459350893053326313050)]
    [(168974,1)] [(168975,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
end ShielddSecurity.TierSelectors631
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.payloadX_checked
#print axioms ShielddSecurity.TierSelectors631.payloadX_checked
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.payloadX_value
#print axioms ShielddSecurity.TierSelectors631.payloadX_value
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.payloadY_checked
#print axioms ShielddSecurity.TierSelectors631.payloadY_checked
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.payloadY_value
#print axioms ShielddSecurity.TierSelectors631.payloadY_value
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family0X_checked
#print axioms ShielddSecurity.TierSelectors631.family0X_checked
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family0X_value
#print axioms ShielddSecurity.TierSelectors631.family0X_value
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family0Y_checked
#print axioms ShielddSecurity.TierSelectors631.family0Y_checked
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family0Y_value
#print axioms ShielddSecurity.TierSelectors631.family0Y_value
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family2X_checked
#print axioms ShielddSecurity.TierSelectors631.family2X_checked
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family2X_value
#print axioms ShielddSecurity.TierSelectors631.family2X_value
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family2Y_checked
#print axioms ShielddSecurity.TierSelectors631.family2Y_checked
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family2Y_value
#print axioms ShielddSecurity.TierSelectors631.family2Y_value
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family3X_checked
#print axioms ShielddSecurity.TierSelectors631.family3X_checked
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family3X_value
#print axioms ShielddSecurity.TierSelectors631.family3X_value
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family3Y_checked
#print axioms ShielddSecurity.TierSelectors631.family3Y_checked
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family3Y_value
#print axioms ShielddSecurity.TierSelectors631.family3Y_value
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family4X_checked
#print axioms ShielddSecurity.TierSelectors631.family4X_checked
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family4X_value
#print axioms ShielddSecurity.TierSelectors631.family4X_value
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family4Y_checked
#print axioms ShielddSecurity.TierSelectors631.family4Y_checked
set_option pp.all true in
#check @ShielddSecurity.TierSelectors631.family4Y_value
#print axioms ShielddSecurity.TierSelectors631.family4Y_value
