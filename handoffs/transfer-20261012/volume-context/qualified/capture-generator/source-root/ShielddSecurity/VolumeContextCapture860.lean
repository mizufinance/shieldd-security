-- GENERATED from maintained exact capture; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeContextCapture860
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 MapArithmeticAdapter704
noncomputable def feeExternalEntry : Entry := ⟨936133,false,[(7607,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(108458,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)],[(121562,1)],[(121563,1)],98824,[⟨[(7607,1),(108458,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184511)],[(121563,1)]⟩,⟨[(7607,1),(108458,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(121562,4),(121563,1)]⟩]⟩
theorem feeExternal_checked : check feeExternalEntry=true := by decide +kernel
theorem feeExternal_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 121562=eval rho [(7607,1),(200692,-1)]*eval rho [(108458,-1),(200692,1)] := by
  have result := MapArithmeticAdapter704.equation feeExternalEntry feeExternal_checked rho arithmetic
  have left : canonical p [(7607,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=canonical p [(7607,1),(200692,-1)] := by decide +kernel
  have right : canonical p [(108458,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)]=canonical p [(108458,-1),(200692,1)] := by decide +kernel
  simp only [feeExternalEntry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ left,canonical_equal rho _ _ right] at result
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
noncomputable def row8318 : Row := ⟨[(121562,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩
theorem row8318_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+8318) 1 [row8318]=true := by decide +kernel

theorem row8318_satisfies (rho : Nat → F) (zero : rho 121562=0) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8318+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row8318] row8318_captured rho).mp
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(121562,52435875175126190479447740508185965837690552500527637822603658699938581184512)]*eval rho [(121562,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=eval rho []
  simp only [eval,zero,mul_zero,add_zero]
def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8318+i)) 1

theorem rows (rho : Nat → F) (feeExternal : rho 121562=0) : Rows rho :=
  row8318_satisfies rho feeExternal
end ShielddSecurity.VolumeContextCapture860

set_option pp.all true in
#check @ShielddSecurity.VolumeContextCapture860.feeExternal_checked
#print axioms ShielddSecurity.VolumeContextCapture860.feeExternal_checked

set_option pp.all true in
#check @ShielddSecurity.VolumeContextCapture860.feeExternal_equation
#print axioms ShielddSecurity.VolumeContextCapture860.feeExternal_equation

set_option pp.all true in
#check @ShielddSecurity.VolumeContextCapture860.row8318_captured
#print axioms ShielddSecurity.VolumeContextCapture860.row8318_captured

set_option pp.all true in
#check @ShielddSecurity.VolumeContextCapture860.row8318_satisfies
#print axioms ShielddSecurity.VolumeContextCapture860.row8318_satisfies

set_option pp.all true in
#check @ShielddSecurity.VolumeContextCapture860.Rows
#print axioms ShielddSecurity.VolumeContextCapture860.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumeContextCapture860.rows
#print axioms ShielddSecurity.VolumeContextCapture860.rows
