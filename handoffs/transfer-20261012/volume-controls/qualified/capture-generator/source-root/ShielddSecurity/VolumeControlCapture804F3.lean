-- GENERATED from maintained exact capture; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeControlCapture804F3
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 MapArithmeticAdapter704
noncomputable def inverseEntry : Entry := ⟨766103,false,[(1513,1),(1751,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(7604,1)],[(108454,1)],[(108455,1)],85716,[⟨[(1513,1),(1751,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7604,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(108455,1)]⟩,⟨[(1513,1),(1751,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7604,1)],[(108454,4),(108455,1)]⟩]⟩
noncomputable def inverseRows : List Row := [⟨[(7603,1),(108454,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩]
theorem inverse_checked : check inverseEntry=true := by decide +kernel

theorem inverse_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108454=(rho 1513-rho 1751)*rho 7604 := by
  have result := MapArithmeticAdapter704.equation inverseEntry inverse_checked rho arithmetic
  have shape : canonical p [(1513,1),(1751,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=canonical p [(1513,1),(1751,-1)] := by decide +kernel
  simp only [inverseEntry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ shape] at result
  simpa only [eval,Int.cast_one,one_mul,Int.cast_neg,add_zero,neg_mul,sub_eq_add_neg] using result

theorem inverse_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+7471) 1 inverseRows=true := by decide +kernel
noncomputable def zeroEntry : Entry := ⟨766106,false,[(1513,1),(1751,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(7603,1)],[(108456,1)],[(108457,1)],85718,[⟨[(1513,1),(1751,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7603,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(108457,1)]⟩,⟨[(1513,1),(1751,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7603,1)],[(108456,4),(108457,1)]⟩]⟩
noncomputable def zeroRows : List Row := [⟨[(108456,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩]
theorem zero_checked : check zeroEntry=true := by decide +kernel

theorem zero_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108456=(rho 1513-rho 1751)*rho 7603 := by
  have result := MapArithmeticAdapter704.equation zeroEntry zero_checked rho arithmetic
  have shape : canonical p [(1513,1),(1751,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=canonical p [(1513,1),(1751,-1)] := by decide +kernel
  simp only [zeroEntry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ shape] at result
  simpa only [eval,Int.cast_one,one_mul,Int.cast_neg,add_zero,neg_mul,sub_eq_add_neg] using result

theorem zero_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+7472) 1 zeroRows=true := by decide +kernel
theorem rows (rho : Nat → F) (one : rho copy=1)
    (inverse : rho 108454=1-rho 7603) (zero : rho 108456=0) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7471+i)) 1 ∧
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7472+i)) 1 := by
  constructor
  · apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+7471) 1 inverseRows inverse_captured rho).mp
    intro row member
    simp only [inverseRows,List.mem_cons,List.not_mem_nil,or_false] at member
    subst row
    change eval rho [(7603,1),(108454,1),(copy,(p:Int)-1)]*eval rho [(7603,1),(108454,1),(copy,(p:Int)-1)]=eval rho []
    have shape : canonical p [(7603,1),(108454,1),(copy,(p:Int)-1)]=canonical p [(7603,1),(108454,1),(copy,-1)] := by decide +kernel
    rw [canonical_equal rho _ _ shape]
    simp only [eval,Int.cast_one,one_mul,Int.cast_neg,add_zero,one,inverse]
    ring
  · apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+7472) 1 zeroRows zero_captured rho).mp
    intro row member
    simp only [zeroRows,List.mem_cons,List.not_mem_nil,or_false] at member
    subst row
    change eval rho [(108456,(p:Int)-1)]*eval rho [(108456,(p:Int)-1)]=eval rho []
    simp only [eval,add_zero,zero,mul_zero]
end ShielddSecurity.VolumeControlCapture804F3

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804F3.inverse_checked
#print axioms ShielddSecurity.VolumeControlCapture804F3.inverse_checked

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804F3.inverse_equation
#print axioms ShielddSecurity.VolumeControlCapture804F3.inverse_equation

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804F3.inverse_captured
#print axioms ShielddSecurity.VolumeControlCapture804F3.inverse_captured

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804F3.zero_checked
#print axioms ShielddSecurity.VolumeControlCapture804F3.zero_checked

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804F3.zero_equation
#print axioms ShielddSecurity.VolumeControlCapture804F3.zero_equation

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804F3.zero_captured
#print axioms ShielddSecurity.VolumeControlCapture804F3.zero_captured

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804F3.rows
#print axioms ShielddSecurity.VolumeControlCapture804F3.rows
