/- Generated from maintained exact nonidentity capture; edit generator or template. -/
import ShielddSecurity.MapArithmeticAdapter704
import ShielddSecurity.DetectionBase627
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.DetectionNonidentityCapture763
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 MapArithmeticAdapter704
noncomputable def entry : Entry := ⟨129138,false,[(1503,1)],[(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33794,1)],[(33795,1)],11056,[⟨[(1503,1),(33790,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,34603644889727414955607589073122773917057272212473650571642302237253952351023)],[(33795,1)]⟩,⟨[(1503,1),(33790,1),(200692,17832230285398775523840151435063191920633280288053987250961356462684628833490)],[(33794,4),(33795,1)]⟩]⟩
noncomputable def assertionRows : List Row := [⟨[(33794,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)],[]⟩]

theorem checked : check entry=true := by decide +kernel

theorem equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 33794=rho 1503*eval rho DetectionBase627.baseX := by
  have result := MapArithmeticAdapter704.equation entry checked rho arithmetic
  simpa only [entry,DetectionBase627.baseX,eval,Int.cast_one,one_mul,add_zero,Bool.false_eq_true,if_false] using result

theorem captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+1468) 1 assertionRows=true := by decide +kernel

theorem rows (rho : Nat → F) (one : rho copy=1) (inverse : rho 33794=1) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+1468+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+1468) 1 assertionRows captured rho).mp
  intro row member
  simp only [assertionRows,List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(33794,(p:Int)-1),(copy,1)]*eval rho [(33794,(p:Int)-1),(copy,1)]=eval rho []
  have shape : canonical p [(33794,(p:Int)-1),(copy,1)]=canonical p [(33794,-1),(copy,1)] := by decide +kernel
  rw [canonical_equal rho _ _ shape]
  simp only [eval,Int.cast_neg,Int.cast_one,one_mul,neg_mul,one,inverse,add_zero,neg_add_cancel,mul_zero,zero_mul]
end ShielddSecurity.DetectionNonidentityCapture763

set_option pp.all true in
#check @ShielddSecurity.DetectionNonidentityCapture763.checked
#print axioms ShielddSecurity.DetectionNonidentityCapture763.checked

set_option pp.all true in
#check @ShielddSecurity.DetectionNonidentityCapture763.equation
#print axioms ShielddSecurity.DetectionNonidentityCapture763.equation

set_option pp.all true in
#check @ShielddSecurity.DetectionNonidentityCapture763.captured
#print axioms ShielddSecurity.DetectionNonidentityCapture763.captured

set_option pp.all true in
#check @ShielddSecurity.DetectionNonidentityCapture763.rows
#print axioms ShielddSecurity.DetectionNonidentityCapture763.rows
