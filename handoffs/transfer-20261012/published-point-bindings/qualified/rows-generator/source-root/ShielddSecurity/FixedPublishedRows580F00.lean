-- GENERATED from entries.json by generate.py. Do not hand edit.
import ShielddSecurity.PointEqualityAdapter440
import ShielddSecurity.VariableWindowColumns449
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedPublishedRows580F00
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
def entry : PointEqualityAdapter440.Entry :=
  ⟨[(5433,1)],[(5434,1)],[(4922,1)],[(4923,1)],5292,[⟨[(4922,52435875175126190479447740508185965837690552500527637822603658699938581184512),(5433,1)],[]⟩,⟨[(4923,52435875175126190479447740508185965837690552500527637822603658699938581184512),(5434,1)],[]⟩]⟩
theorem checked : PointEqualityAdapter440.check entry=true := by decide +kernel
theorem rows_iff {F : Type} [Field F] [CharP F p] (rho : Nat → F) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+5292+i)) 2 ↔
    VariableWindowColumns449.columnPoint rho 5433=VariableWindowColumns449.columnPoint rho 4922 := by
  have equivalence := PointEqualityAdapter440.equality_iff entry checked rho
  change SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+5292+i)) 2 ↔
    Group.Point.mk (eval rho [(5433,1)]) (eval rho [(5434,1)])=
    Group.Point.mk (eval rho [(4922,1)]) (eval rho [(4923,1)]) at equivalence
  simpa only [eval,Int.cast_one,one_mul,add_zero,VariableWindowColumns449.columnPoint] using equivalence

end ShielddSecurity.FixedPublishedRows580F00

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580F00.entry
#print axioms ShielddSecurity.FixedPublishedRows580F00.entry

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580F00.checked
#print axioms ShielddSecurity.FixedPublishedRows580F00.checked

set_option pp.all true in
#check @ShielddSecurity.FixedPublishedRows580F00.rows_iff
#print axioms ShielddSecurity.FixedPublishedRows580F00.rows_iff
