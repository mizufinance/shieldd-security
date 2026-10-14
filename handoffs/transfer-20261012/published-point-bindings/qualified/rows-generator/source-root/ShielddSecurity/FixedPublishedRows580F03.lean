-- GENERATED from entries.json by generate.py. Do not hand edit.
import ShielddSecurity.PointEqualityAdapter440
import ShielddSecurity.VariableWindowColumns449
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedPublishedRows580F03
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
def entry : PointEqualityAdapter440.Entry :=
  ⟨[(10586,1)],[(10587,1)],[(10079,1)],[(10080,1)],10366,[⟨[(10079,52435875175126190479447740508185965837690552500527637822603658699938581184512),(10586,1)],[]⟩,⟨[(10080,52435875175126190479447740508185965837690552500527637822603658699938581184512),(10587,1)],[]⟩]⟩
theorem checked : PointEqualityAdapter440.check entry=true := by decide +kernel
theorem rows_iff {F : Type} [Field F] [CharP F p] (rho : Nat → F) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+10366+i)) 2 ↔
    VariableWindowColumns449.columnPoint rho 10586=VariableWindowColumns449.columnPoint rho 10079 := by
  have equivalence := PointEqualityAdapter440.equality_iff entry checked rho
  change SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+10366+i)) 2 ↔
    Group.Point.mk (eval rho [(10586,1)]) (eval rho [(10587,1)])=
    Group.Point.mk (eval rho [(10079,1)]) (eval rho [(10080,1)]) at equivalence
  simpa only [eval,Int.cast_one,one_mul,add_zero,VariableWindowColumns449.columnPoint] using equivalence

end ShielddSecurity.FixedPublishedRows580F03

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580F03.entry
#print axioms ShielddSecurity.FixedPublishedRows580F03.entry

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580F03.checked
#print axioms ShielddSecurity.FixedPublishedRows580F03.checked

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580F03.rows_iff
#print axioms ShielddSecurity.FixedPublishedRows580F03.rows_iff
