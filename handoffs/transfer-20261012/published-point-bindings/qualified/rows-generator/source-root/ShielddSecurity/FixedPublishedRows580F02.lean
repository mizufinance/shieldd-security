-- GENERATED from entries.json by generate.py. Do not hand edit.
import ShielddSecurity.PointEqualityAdapter440
import ShielddSecurity.VariableWindowColumns449
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedPublishedRows580F02
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
def entry : PointEqualityAdapter440.Entry :=
  ⟨[(9054,1)],[(9055,1)],[(8547,1)],[(8548,1)],8826,[⟨[(8547,52435875175126190479447740508185965837690552500527637822603658699938581184512),(9054,1)],[]⟩,⟨[(8548,52435875175126190479447740508185965837690552500527637822603658699938581184512),(9055,1)],[]⟩]⟩
theorem checked : PointEqualityAdapter440.check entry=true := by decide +kernel
theorem rows_iff {F : Type} [Field F] [CharP F p] (rho : Nat → F) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8826+i)) 2 ↔
    VariableWindowColumns449.columnPoint rho 9054=VariableWindowColumns449.columnPoint rho 8547 := by
  have equivalence := PointEqualityAdapter440.equality_iff entry checked rho
  change SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8826+i)) 2 ↔
    Group.Point.mk (eval rho [(9054,1)]) (eval rho [(9055,1)])=
    Group.Point.mk (eval rho [(8547,1)]) (eval rho [(8548,1)]) at equivalence
  simpa only [eval,Int.cast_one,one_mul,add_zero,VariableWindowColumns449.columnPoint] using equivalence

end ShielddSecurity.FixedPublishedRows580F02

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580F02.entry
#print axioms ShielddSecurity.FixedPublishedRows580F02.entry

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580F02.checked
#print axioms ShielddSecurity.FixedPublishedRows580F02.checked

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580F02.rows_iff
#print axioms ShielddSecurity.FixedPublishedRows580F02.rows_iff
