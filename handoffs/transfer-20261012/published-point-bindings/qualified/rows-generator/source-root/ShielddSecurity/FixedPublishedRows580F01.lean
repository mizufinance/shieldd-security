-- GENERATED from entries.json by generate.py. Do not hand edit.
import ShielddSecurity.PointEqualityAdapter440
import ShielddSecurity.VariableWindowColumns449
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedPublishedRows580F01
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
def entry : PointEqualityAdapter440.Entry :=
  ⟨[(6837,1)],[(6838,1)],[(6326,1)],[(6327,1)],6695,[⟨[(6326,52435875175126190479447740508185965837690552500527637822603658699938581184512),(6837,1)],[]⟩,⟨[(6327,52435875175126190479447740508185965837690552500527637822603658699938581184512),(6838,1)],[]⟩]⟩
theorem checked : PointEqualityAdapter440.check entry=true := by decide +kernel
theorem rows_iff {F : Type} [Field F] [CharP F p] (rho : Nat → F) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+6695+i)) 2 ↔
    VariableWindowColumns449.columnPoint rho 6837=VariableWindowColumns449.columnPoint rho 6326 := by
  have equivalence := PointEqualityAdapter440.equality_iff entry checked rho
  change SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+6695+i)) 2 ↔
    Group.Point.mk (eval rho [(6837,1)]) (eval rho [(6838,1)])=
    Group.Point.mk (eval rho [(6326,1)]) (eval rho [(6327,1)]) at equivalence
  simpa only [eval,Int.cast_one,one_mul,add_zero,VariableWindowColumns449.columnPoint] using equivalence

end ShielddSecurity.FixedPublishedRows580F01

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580F01.entry
#print axioms ShielddSecurity.FixedPublishedRows580F01.entry

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580F01.checked
#print axioms ShielddSecurity.FixedPublishedRows580F01.checked

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580F01.rows_iff
#print axioms ShielddSecurity.FixedPublishedRows580F01.rows_iff
