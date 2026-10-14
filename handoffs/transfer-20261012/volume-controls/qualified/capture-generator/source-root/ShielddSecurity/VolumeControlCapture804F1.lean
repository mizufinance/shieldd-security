-- GENERATED from maintained exact capture; do not edit.
import ShielddSecurity.MapArithmeticAdapter704
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeControlCapture804F1
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 MapArithmeticAdapter704
noncomputable def inverseEntry : Entry := ⟨766087,false,[(1505,1),(1743,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(7600,1)],[(108442,1)],[(108443,1)],85704,[⟨[(1505,1),(1743,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7600,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(108443,1)]⟩,⟨[(1505,1),(1743,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7600,1)],[(108442,4),(108443,1)]⟩]⟩
noncomputable def inverseRows : List Row := [⟨[(7599,1),(108442,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩]
theorem inverse_checked : check inverseEntry=true := by decide +kernel

theorem inverse_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108442=(rho 1505-rho 1743)*rho 7600 := by
  have result := MapArithmeticAdapter704.equation inverseEntry inverse_checked rho arithmetic
  have shape : canonical p [(1505,1),(1743,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=canonical p [(1505,1),(1743,-1)] := by decide +kernel
  simp only [inverseEntry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ shape] at result
  simpa only [eval,Int.cast_one,one_mul,Int.cast_neg,add_zero,neg_mul,sub_eq_add_neg] using result

theorem inverse_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+7465) 1 inverseRows=true := by decide +kernel
noncomputable def zeroEntry : Entry := ⟨766090,false,[(1505,1),(1743,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(7599,1)],[(108444,1)],[(108445,1)],85706,[⟨[(1505,1),(1743,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7599,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(108445,1)]⟩,⟨[(1505,1),(1743,52435875175126190479447740508185965837690552500527637822603658699938581184512),(7599,1)],[(108444,4),(108445,1)]⟩]⟩
noncomputable def zeroRows : List Row := [⟨[(108444,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩]
theorem zero_checked : check zeroEntry=true := by decide +kernel

theorem zero_equation (rho : Nat → F) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    rho 108444=(rho 1505-rho 1743)*rho 7599 := by
  have result := MapArithmeticAdapter704.equation zeroEntry zero_checked rho arithmetic
  have shape : canonical p [(1505,1),(1743,52435875175126190479447740508185965837690552500527637822603658699938581184512)]=canonical p [(1505,1),(1743,-1)] := by decide +kernel
  simp only [zeroEntry,Bool.false_eq_true,if_false] at result
  rw [canonical_equal rho _ _ shape] at result
  simpa only [eval,Int.cast_one,one_mul,Int.cast_neg,add_zero,neg_mul,sub_eq_add_neg] using result

theorem zero_captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+7466) 1 zeroRows=true := by decide +kernel
theorem rows (rho : Nat → F) (one : rho copy=1)
    (inverse : rho 108442=1-rho 7599) (zero : rho 108444=0) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7465+i)) 1 ∧
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+7466+i)) 1 := by
  constructor
  · apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+7465) 1 inverseRows inverse_captured rho).mp
    intro row member
    simp only [inverseRows,List.mem_cons,List.not_mem_nil,or_false] at member
    subst row
    change eval rho [(7599,1),(108442,1),(copy,(p:Int)-1)]*eval rho [(7599,1),(108442,1),(copy,(p:Int)-1)]=eval rho []
    have shape : canonical p [(7599,1),(108442,1),(copy,(p:Int)-1)]=canonical p [(7599,1),(108442,1),(copy,-1)] := by decide +kernel
    rw [canonical_equal rho _ _ shape]
    simp only [eval,Int.cast_one,one_mul,Int.cast_neg,add_zero,one,inverse]
    ring
  · apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+7466) 1 zeroRows zero_captured rho).mp
    intro row member
    simp only [zeroRows,List.mem_cons,List.not_mem_nil,or_false] at member
    subst row
    change eval rho [(108444,(p:Int)-1)]*eval rho [(108444,(p:Int)-1)]=eval rho []
    simp only [eval,add_zero,zero,mul_zero]
end ShielddSecurity.VolumeControlCapture804F1

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804F1.inverse_checked
#print axioms ShielddSecurity.VolumeControlCapture804F1.inverse_checked

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804F1.inverse_equation
#print axioms ShielddSecurity.VolumeControlCapture804F1.inverse_equation

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804F1.inverse_captured
#print axioms ShielddSecurity.VolumeControlCapture804F1.inverse_captured

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804F1.zero_checked
#print axioms ShielddSecurity.VolumeControlCapture804F1.zero_checked

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804F1.zero_equation
#print axioms ShielddSecurity.VolumeControlCapture804F1.zero_equation

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804F1.zero_captured
#print axioms ShielddSecurity.VolumeControlCapture804F1.zero_captured

set_option pp.all true in
#check @ShielddSecurity.VolumeControlCapture804F1.rows
#print axioms ShielddSecurity.VolumeControlCapture804F1.rows
