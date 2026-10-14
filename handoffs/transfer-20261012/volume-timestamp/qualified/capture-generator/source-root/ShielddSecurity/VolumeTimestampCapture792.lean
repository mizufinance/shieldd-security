-- GENERATED from maintained data and template; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeTimestampCapture792
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01
noncomputable def rows : List Row := [⟨[(7,1),(7608,52435875175126190479447740508185965837690552500527637822603658699938581098113),(7609,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩]
theorem checked : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+7610) 1 rows=true := by decide +kernel

def Rows (rho : Nat → F) : Prop := SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7610+i)) 1

theorem satisfies (rho : Nat → F) (relation : rho 7=86400*rho 7608+rho 7609) : Rows rho := by
  apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+7610) 1 rows checked rho).mp
  intro row member
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(7,1),(7608,(p:Int)-86400),(7609,(p:Int)-1)]*
    eval rho [(7,1),(7608,(p:Int)-86400),(7609,(p:Int)-1)]=eval rho []
  have shape : canonical p [(7,1),(7608,(p:Int)-86400),(7609,(p:Int)-1)]=
    canonical p [(7,1),(7608,-86400),(7609,-1)] := by decide +kernel
  rw [canonical_equal rho _ _ shape]
  simp only [eval,Int.cast_one,one_mul,Int.cast_neg,Int.cast_ofNat,add_zero,relation]
  ring
end ShielddSecurity.VolumeTimestampCapture792

set_option pp.all true in
#check @ShielddSecurity.VolumeTimestampCapture792.checked
#print axioms ShielddSecurity.VolumeTimestampCapture792.checked

set_option pp.all true in
#check @ShielddSecurity.VolumeTimestampCapture792.Rows
#print axioms ShielddSecurity.VolumeTimestampCapture792.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumeTimestampCapture792.satisfies
#print axioms ShielddSecurity.VolumeTimestampCapture792.satisfies
