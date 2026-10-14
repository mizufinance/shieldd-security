/- Generated from maintained exact nonidentity capture; edit generator or template. -/
import ShielddSecurity.MapArithmeticAdapter704
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.OutputAmountCapture771
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 MapArithmeticAdapter704
noncomputable def entry : Entry := ⟨670587,false,[(4919,1)],[(4789,1)],[(87782,1)],[(87783,1)],65044,[⟨[(4789,52435875175126190479447740508185965837690552500527637822603658699938581184512),(4919,1)],[(87783,1)]⟩,⟨[(4789,1),(4919,1)],[(87782,4),(87783,1)]⟩]⟩
noncomputable def assertionRows : List Row := [⟨[(87782,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)],[]⟩]

theorem checked : check entry=true := by decide +kernel

theorem equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 87782=rho 4919*rho 4789 := by
  have result := MapArithmeticAdapter704.equation entry checked rho arithmetic
  simpa only [entry,eval,Int.cast_one,one_mul,add_zero,Bool.false_eq_true,if_false] using result

theorem captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+4783) 1 assertionRows=true := by decide +kernel

theorem rows (rho : Nat → F) (one : rho copy=1) (inverse : rho 87782=1) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+4783+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+4783) 1 assertionRows captured rho).mp
  intro row member
  simp only [assertionRows,List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(87782,(p:Int)-1),(copy,1)]*eval rho [(87782,(p:Int)-1),(copy,1)]=eval rho []
  have shape : canonical p [(87782,(p:Int)-1),(copy,1)]=canonical p [(87782,-1),(copy,1)] := by decide +kernel
  rw [canonical_equal rho _ _ shape]
  simp only [eval,Int.cast_neg,Int.cast_one,one_mul,neg_mul,one,inverse,add_zero,neg_add_cancel,mul_zero,zero_mul]
end ShielddSecurity.OutputAmountCapture771

set_option pp.all true in
#check @ShielddSecurity.OutputAmountCapture771.checked
#print axioms ShielddSecurity.OutputAmountCapture771.checked

set_option pp.all true in
#check @ShielddSecurity.OutputAmountCapture771.equation
#print axioms ShielddSecurity.OutputAmountCapture771.equation

set_option pp.all true in
#check @ShielddSecurity.OutputAmountCapture771.captured
#print axioms ShielddSecurity.OutputAmountCapture771.captured

set_option pp.all true in
#check @ShielddSecurity.OutputAmountCapture771.rows
#print axioms ShielddSecurity.OutputAmountCapture771.rows
