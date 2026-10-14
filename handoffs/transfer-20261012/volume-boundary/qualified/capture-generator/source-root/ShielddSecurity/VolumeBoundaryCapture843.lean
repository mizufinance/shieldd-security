-- GENERATED from maintained exact capture; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeBoundaryCapture843
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 MapArithmeticAdapter704
noncomputable def dayEntry : Entry := ⟨766660,false,[(7607,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,2)],[(7608,86400)],[(108480,1)],[(108481,1)],85742,[⟨[(7607,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7608,52435875175126190479447740508185965837690552500527637822603658699938581098113),(200692,2)],[(108481,1)]⟩,⟨[(7607,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7608,86400),(200692,2)],[(108480,4),(108481,1)]⟩]⟩
theorem day_checked : check dayEntry=true := by decide +kernel
theorem day_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108480=eval rho [(7607,-1),(200692,2)]*eval rho [(7608,86400)] := by
  have result := MapArithmeticAdapter704.equation dayEntry day_checked rho arithmetic
  have left : canonical p [(7607,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,2)]=canonical p [(7607,-1),(200692,2)] := by decide +kernel
  have right : canonical p [(7608,86400)]=canonical p [(7608,86400)] := by decide +kernel
  simp only [dayEntry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ left,canonical_equal rho _ _ right] at result
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
noncomputable def limitEntry : Entry := ⟨774491,false,[(7605,1)],[(8255,1)],[(108908,1)],[(108909,1)],86170,[⟨[(7605,1),(8255,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(108909,1)]⟩,⟨[(7605,1),(8255,1)],[(108908,4),(108909,1)]⟩]⟩
theorem limit_checked : check limitEntry=true := by decide +kernel
theorem limit_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108908=eval rho [(7605,1)]*eval rho [(8255,1)] := by
  have result := MapArithmeticAdapter704.equation limitEntry limit_checked rho arithmetic
  have left : canonical p [(7605,1)]=canonical p [(7605,1)] := by decide +kernel
  have right : canonical p [(8255,1)]=canonical p [(8255,1)] := by decide +kernel
  simp only [limitEntry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ left,canonical_equal rho _ _ right] at result
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
noncomputable def row7611 : Row := ⟨[(7739,1),(108480,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩
theorem row7611_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+7611) 1 [row7611]=true := by decide +kernel

theorem row7611_satisfies (rho : Nat → F) (equal : rho 7739=rho 108480) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7611+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row7611] row7611_captured rho).mp
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(7739,1),(108480,52435875175126190479447740508185965837690552500527637822603658699938581184512)]*eval rho [(7739,1),(108480,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=eval rho []
  have shape : canonical p [(7739,1),(108480,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=canonical p [(7739,1),(108480,-1)] := by decide +kernel
  rw [canonical_equal rho _ _ shape]
  simp only [eval,Int.cast_one,Int.cast_neg,one_mul,add_zero,neg_mul,equal]
  ring
noncomputable def row8262 : Row := ⟨[(108908,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩
theorem row8262_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+8262) 1 [row8262]=true := by decide +kernel

theorem row8262_satisfies (rho : Nat → F) (zero : rho 108908=0) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8262+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row8262] row8262_captured rho).mp
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(108908,52435875175126190479447740508185965837690552500527637822603658699938581184512)]*eval rho [(108908,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=eval rho []
  simp only [eval,zero,mul_zero,add_zero]
def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7611+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8262+i)) 1

theorem rows (rho : Nat → F) (day : rho 7739=rho 108480) (limit : rho 108908=0) : Rows rho :=
  ⟨row7611_satisfies rho day,row8262_satisfies rho limit⟩
end ShielddSecurity.VolumeBoundaryCapture843

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryCapture843.day_checked
#print axioms ShielddSecurity.VolumeBoundaryCapture843.day_checked

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryCapture843.day_equation
#print axioms ShielddSecurity.VolumeBoundaryCapture843.day_equation

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryCapture843.limit_checked
#print axioms ShielddSecurity.VolumeBoundaryCapture843.limit_checked

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryCapture843.limit_equation
#print axioms ShielddSecurity.VolumeBoundaryCapture843.limit_equation

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryCapture843.row7611_captured
#print axioms ShielddSecurity.VolumeBoundaryCapture843.row7611_captured

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryCapture843.row7611_satisfies
#print axioms ShielddSecurity.VolumeBoundaryCapture843.row7611_satisfies

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryCapture843.row8262_captured
#print axioms ShielddSecurity.VolumeBoundaryCapture843.row8262_captured

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryCapture843.row8262_satisfies
#print axioms ShielddSecurity.VolumeBoundaryCapture843.row8262_satisfies

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryCapture843.Rows
#print axioms ShielddSecurity.VolumeBoundaryCapture843.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryCapture843.rows
#print axioms ShielddSecurity.VolumeBoundaryCapture843.rows
