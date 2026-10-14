-- GENERATED from maintained exact capture; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeControlCapture804Context
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 MapArithmeticAdapter704
noncomputable def rows : List Row := [⟨[(7607,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(7607,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)]⟩]
theorem checked : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+7475) 1 rows=true := by decide +kernel

theorem satisfies (rho : Nat → F) (one : rho copy=1)
    (boolean : (rho 7607-1)*(rho 7607-1)=rho 7607-1) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7475+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+7475) 1 rows checked rho).mp
  intro row member
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(7607,1),(copy,(p:Int)-1)]*eval rho [(7607,1),(copy,(p:Int)-1)]=eval rho [(7607,1),(copy,(p:Int)-1)]
  have shape : canonical p [(7607,1),(copy,(p:Int)-1)]=canonical p [(7607,1),(copy,-1)] := by decide +kernel
  rw [canonical_equal rho _ _ shape]
  simpa only [eval,Int.cast_one,one_mul,Int.cast_neg,add_zero,one,neg_mul,mul_one,sub_eq_add_neg] using boolean
end ShielddSecurity.VolumeControlCapture804Context

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804Context.checked
#print axioms ShielddSecurity.VolumeControlCapture804Context.checked

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804Context.satisfies
#print axioms ShielddSecurity.VolumeControlCapture804Context.satisfies
