-- GENERATED from maintained exact capture; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeTransitionCapture828
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 MapArithmeticAdapter704
noncomputable def eligibilityEntry : Entry := ⟨766664,false,[(7605,1)],[(108482,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)],[(108484,1)],[(108485,1)],85746,[⟨[(7605,1),(108482,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(108485,1)]⟩,⟨[(7605,1),(108482,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)],[(108484,4),(108485,1)]⟩]⟩
theorem eligibility_checked : check eligibilityEntry=true := by decide +kernel
theorem eligibility_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108484=eval rho [(7605,1)]*eval rho [(108482,-1),(200692,1)] := by
  have result := MapArithmeticAdapter704.equation eligibilityEntry eligibility_checked rho arithmetic
  have left : canonical p [(7605,1)]=canonical p [(7605,1)] := by decide +kernel
  have right : canonical p [(108482,52435875175126190479447740508185965837690552500527637822603658699938581184512),(200692,1)]=canonical p [(108482,-1),(200692,1)] := by decide +kernel
  simp only [eligibilityEntry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ left,canonical_equal rho _ _ right] at result
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
noncomputable def successorEntry : Entry := ⟨773584,false,[(7605,1)],[(4789,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7741,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7742,1)],[(108906,1)],[(108907,1)],86168,[⟨[(4789,1),(7605,1),(7741,1),(7742,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(108907,1)]⟩,⟨[(4789,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7605,1),(7741,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7742,1)],[(108906,4),(108907,1)]⟩]⟩
theorem successor_checked : check successorEntry=true := by decide +kernel
theorem successor_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108906=eval rho [(7605,1)]*eval rho [(4789,-1),(7741,-1),(7742,1)] := by
  have result := MapArithmeticAdapter704.equation successorEntry successor_checked rho arithmetic
  have left : canonical p [(7605,1)]=canonical p [(7605,1)] := by decide +kernel
  have right : canonical p [(4789,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7741,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7742,1)]=canonical p [(4789,-1),(7741,-1),(7742,1)] := by decide +kernel
  simp only [successorEntry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ left,canonical_equal rho _ _ right] at result
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
noncomputable def newDayEntry : Entry := ⟨774492,false,[(7605,1)],[(7606,1)],[(108910,1)],[(108911,1)],86172,[⟨[(7605,1),(7606,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(108911,1)]⟩,⟨[(7605,1),(7606,1)],[(108910,4),(108911,1)]⟩]⟩
theorem newDay_checked : check newDayEntry=true := by decide +kernel
theorem newDay_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108910=eval rho [(7605,1)]*eval rho [(7606,1)] := by
  have result := MapArithmeticAdapter704.equation newDayEntry newDay_checked rho arithmetic
  have left : canonical p [(7605,1)]=canonical p [(7605,1)] := by decide +kernel
  have right : canonical p [(7606,1)]=canonical p [(7606,1)] := by decide +kernel
  simp only [newDayEntry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ left,canonical_equal rho _ _ right] at result
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
noncomputable def priorEntry : Entry := ⟨774494,false,[(108910,1)],[(7741,1)],[(108912,1)],[(108913,1)],86174,[⟨[(7741,52435875175126190479447740508185965837690552500527637822603658699938581184512),(108910,1)],[(108913,1)]⟩,⟨[(7741,1),(108910,1)],[(108912,4),(108913,1)]⟩]⟩
theorem prior_checked : check priorEntry=true := by decide +kernel
theorem prior_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108912=eval rho [(108910,1)]*eval rho [(7741,1)] := by
  have result := MapArithmeticAdapter704.equation priorEntry prior_checked rho arithmetic
  have left : canonical p [(108910,1)]=canonical p [(108910,1)] := by decide +kernel
  have right : canonical p [(7741,1)]=canonical p [(7741,1)] := by decide +kernel
  simp only [priorEntry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ left,canonical_equal rho _ _ right] at result
  simpa only [eval,Int.cast_one,one_mul,add_zero] using result
noncomputable def row7612 : Row := ⟨[(108484,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩
theorem row7612_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+7612) 1 [row7612]=true := by decide +kernel

theorem row7612_satisfies (rho : Nat → F) (zero : rho 108484=0) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7612+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row7612] row7612_captured rho).mp
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(108484,52435875175126190479447740508185965837690552500527637822603658699938581184512)]*eval rho [(108484,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=eval rho []
  simp only [eval,zero,mul_zero,add_zero]
noncomputable def row8130 : Row := ⟨[(108906,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩
theorem row8130_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+8130) 1 [row8130]=true := by decide +kernel

theorem row8130_satisfies (rho : Nat → F) (zero : rho 108906=0) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8130+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row8130] row8130_captured rho).mp
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(108906,52435875175126190479447740508185965837690552500527637822603658699938581184512)]*eval rho [(108906,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=eval rho []
  simp only [eval,zero,mul_zero,add_zero]
noncomputable def row8263 : Row := ⟨[(108912,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩
theorem row8263_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+8263) 1 [row8263]=true := by decide +kernel

theorem row8263_satisfies (rho : Nat → F) (zero : rho 108912=0) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8263+i)) 1 := by
  apply (CompilerRowSlice63.selected_satisfies_iff _ _ _ [row8263] row8263_captured rho).mp
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  change eval rho [(108912,52435875175126190479447740508185965837690552500527637822603658699938581184512)]*eval rho [(108912,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=eval rho []
  simp only [eval,zero,mul_zero,add_zero]
def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7612+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8130+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8263+i)) 1

theorem rows (rho : Nat → F) (eligibility : rho 108484=0) (successor : rho 108906=0) (prior : rho 108912=0) : Rows rho :=
  ⟨row7612_satisfies rho eligibility,row8130_satisfies rho successor,row8263_satisfies rho prior⟩
end ShielddSecurity.VolumeTransitionCapture828

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.eligibility_checked
#print axioms ShielddSecurity.VolumeTransitionCapture828.eligibility_checked

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.eligibility_equation
#print axioms ShielddSecurity.VolumeTransitionCapture828.eligibility_equation

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.successor_checked
#print axioms ShielddSecurity.VolumeTransitionCapture828.successor_checked

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.successor_equation
#print axioms ShielddSecurity.VolumeTransitionCapture828.successor_equation

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.newDay_checked
#print axioms ShielddSecurity.VolumeTransitionCapture828.newDay_checked

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.newDay_equation
#print axioms ShielddSecurity.VolumeTransitionCapture828.newDay_equation

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.prior_checked
#print axioms ShielddSecurity.VolumeTransitionCapture828.prior_checked

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.prior_equation
#print axioms ShielddSecurity.VolumeTransitionCapture828.prior_equation

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.row7612_captured
#print axioms ShielddSecurity.VolumeTransitionCapture828.row7612_captured

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.row7612_satisfies
#print axioms ShielddSecurity.VolumeTransitionCapture828.row7612_satisfies

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.row8130_captured
#print axioms ShielddSecurity.VolumeTransitionCapture828.row8130_captured

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.row8130_satisfies
#print axioms ShielddSecurity.VolumeTransitionCapture828.row8130_satisfies

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.row8263_captured
#print axioms ShielddSecurity.VolumeTransitionCapture828.row8263_captured

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.row8263_satisfies
#print axioms ShielddSecurity.VolumeTransitionCapture828.row8263_satisfies

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.Rows
#print axioms ShielddSecurity.VolumeTransitionCapture828.Rows

set_option pp.all true in
#check @ShielddSecurity.VolumeTransitionCapture828.rows
#print axioms ShielddSecurity.VolumeTransitionCapture828.rows
