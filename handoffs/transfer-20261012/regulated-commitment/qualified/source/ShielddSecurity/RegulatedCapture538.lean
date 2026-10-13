import ShielddSecurity.AuthorizationHash530C57
import ShielddSecurity.VariableOperationAdapter434
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CompilerRowSlice63
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegulatedCapture538
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
def ringRows : List Row := [⟨[(10,1),(24,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,29108985603249989484651727880329493522712908252517904247459350893053326313050)],[(33799,1)]⟩,⟨[(10,1),(24,1),(200692,23326889571876200994796012627856472314977644248009733575144307806885254871463)],[(33798,4),(33799,1)]⟩]
def gatedRows : List Row := [⟨[(10,1),(1528,1),(61920,37946758672832325014252119803087263268540590333534118888651318913020744680638),(61924,39310451208185536146735852932245849007745889233114307640726645642245394822974),(61928,14653970678176228351970509534753747945310621286237886970104944815862786477306)],[(61931,1)]⟩,⟨[(10,1),(1528,52435875175126190479447740508185965837690552500527637822603658699938581184512),(61920,14489116502293865465195620705098702569149962166993518933952339786917836503875),(61924,13125423966940654332711887575940116829944663267413330181877013057693186361539),(61928,37781904496949962127477230973432217892379931214289750852498713884075794707207)],[(61930,4),(61931,1)]⟩]
def actualRows : List Row := [⟨[(61930,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩]
theorem ring_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 11060 2 ringRows=true := by decide +kernel
theorem gate_checked : CompilerRowSlice63.check CapturedFullArithmetic52.rowAt 39192 2 gatedRows=true := by decide +kernel
theorem ring_y (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 33798=rho 10*(rho 24-(29108985603249989484651727880329493522712908252517904247459350893053326313050:F)*rho copy) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 11060 2 ringRows ring_checked (by decide) rho arithmetic
  have value := checked_product_sound rho ringRows [(10,1)]
    [(24,1),(copy,-29108985603249989484651727880329493522712908252517904247459350893053326313050)]
    [(33798,1)] [(33799,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval,Int.cast_one,one_mul,add_zero,Int.cast_neg,Int.cast_ofNat,neg_mul,sub_eq_add_neg] using value
theorem gate_value (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 61930=rho 10*(eval rho AuthorizationHash530C57.result-rho 1528) := by
  have sat := CompilerRowSlice63.of_full_satisfies CapturedFullArithmetic52.rowAt 177954 39192 2 gatedRows gate_checked (by decide) rho arithmetic
  have value := checked_product_sound rho gatedRows [(10,1)]
    (subtract AuthorizationHash530C57.result [(1528,1)]) [(61930,1)] [(61931,1)] four_ne_zero sat (by decide +kernel) (by decide +kernel)
  simpa only [eval_subtract,eval,Int.cast_one,one_mul,add_zero] using value
def templates : List Row := [⟨subtract [] [(61930,1)],[]⟩]
theorem actual_checked : CompilerRowSlice63.check CapturedFullRelation58.rowAt 181726 1 actualRows=true := by decide +kernel
theorem forward_checked : VariableOperationAdapter434.covers templates actualRows=true := by decide +kernel
theorem reverse_checked : VariableOperationAdapter434.covers actualRows templates=true := by decide +kernel
def Rows (rho : Nat → F) := SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (181726+i)) 1
theorem rows_iff (rho : Nat → F) : Rows rho ↔ rho 61930=0 := by
  have actual : Rows rho ↔ Satisfies rho actualRows :=
    (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt 181726 1 actualRows actual_checked rho).symm
  rw [actual]
  have equivalent : Satisfies rho actualRows ↔ Satisfies rho templates :=
    ⟨transfer rho _ _ forward_checked,transfer rho _ _ reverse_checked⟩
  rw [equivalent]
  simp only [templates,Satisfies,List.mem_singleton,forall_eq,eval,VariableDoubleTemplate431.equality_row]
  simp only [eval,Int.cast_one,one_mul,add_zero,eq_comm]
end ShielddSecurity.RegulatedCapture538
set_option pp.all true in
#check @ShielddSecurity.RegulatedCapture538.ring_checked
#print axioms ShielddSecurity.RegulatedCapture538.ring_checked
set_option pp.all true in
#check @ShielddSecurity.RegulatedCapture538.gate_checked
#print axioms ShielddSecurity.RegulatedCapture538.gate_checked
set_option pp.all true in
#check @ShielddSecurity.RegulatedCapture538.ring_y
#print axioms ShielddSecurity.RegulatedCapture538.ring_y
set_option pp.all true in
#check @ShielddSecurity.RegulatedCapture538.gate_value
#print axioms ShielddSecurity.RegulatedCapture538.gate_value
set_option pp.all true in
#check @ShielddSecurity.RegulatedCapture538.actual_checked
#print axioms ShielddSecurity.RegulatedCapture538.actual_checked
set_option pp.all true in
#check @ShielddSecurity.RegulatedCapture538.forward_checked
#print axioms ShielddSecurity.RegulatedCapture538.forward_checked
set_option pp.all true in
#check @ShielddSecurity.RegulatedCapture538.reverse_checked
#print axioms ShielddSecurity.RegulatedCapture538.reverse_checked
set_option pp.all true in
#check @ShielddSecurity.RegulatedCapture538.Rows
#print axioms ShielddSecurity.RegulatedCapture538.Rows
set_option pp.all true in
#check @ShielddSecurity.RegulatedCapture538.rows_iff
#print axioms ShielddSecurity.RegulatedCapture538.rows_iff
