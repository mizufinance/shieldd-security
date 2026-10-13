import ShielddSecurity.TransmissionCapture468
import ShielddSecurity.VariableWindowColumns449
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.TransmissionRows470
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
attribute [local irreducible] CapturedFullRelation58.rowAt PointEqualityAdapter440.check

def entry : PointEqualityAdapter440.Entry := TransmissionCapture468.entries[0]
theorem checked : PointEqualityAdapter440.check entry=true := by
  have member : entry∈TransmissionCapture468.entries := List.getElem_mem (by decide)
  exact List.all_eq_true.mp TransmissionCapture468.checked entry member

theorem rows_iff {F : Type} [Field F] [CharP F p] (rho : Nat → F) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+3013+i)) 2 ↔
    VariableWindowColumns449.columnPoint rho 3007=VariableWindowColumns449.columnPoint rho 1512 := by
  have equivalence := PointEqualityAdapter440.equality_iff entry checked rho
  change SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+3013+i)) 2 ↔
    Group.Point.mk (eval rho [(3007,1)]) (eval rho [(3008,1)])=
    Group.Point.mk (eval rho [(1512,1)]) (eval rho [(1513,1)]) at equivalence
  simpa only [eval,Int.cast_one,one_mul,add_zero,VariableWindowColumns449.columnPoint] using equivalence
end ShielddSecurity.TransmissionRows470

set_option pp.all true in
#check @ShielddSecurity.TransmissionRows470.entry
#print axioms ShielddSecurity.TransmissionRows470.entry

set_option pp.all true in
#check @ShielddSecurity.TransmissionRows470.checked
#print axioms ShielddSecurity.TransmissionRows470.checked

set_option pp.all true in
#check @ShielddSecurity.TransmissionRows470.rows_iff
#print axioms ShielddSecurity.TransmissionRows470.rows_iff
