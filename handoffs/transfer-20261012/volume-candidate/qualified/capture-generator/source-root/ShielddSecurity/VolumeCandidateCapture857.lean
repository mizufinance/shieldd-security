-- GENERATED. Do not hand edit.
import ShielddSecurity.VolumeCandidateCapture857A
import ShielddSecurity.VolumeCandidateCapture857B
import ShielddSecurity.CompilerRowSlice63
import ShielddSecurity.CapturedFullRelation58
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeCandidateCapture857
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt fieldBinary
def Rows (rho : Nat → F) : Prop :=
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8129+i)) 1 ∧
  SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+8261+i)) 1

theorem rows (rho : Nat → F)
    (candidate : -rho 4789-rho 7741+fieldBinary ((List.range' 8127 128).map rho)=0)
    (difference : fieldBinary ((List.range' 7999 128).map rho)-fieldBinary ((List.range' 8127 128).map rho)+(2:F)^128*rho 8255-rho 8256=0) : Rows rho :=
  ⟨row8129_satisfies rho candidate,row8261_satisfies rho difference⟩

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateCapture857.rows
#print axioms ShielddSecurity.VolumeCandidateCapture857.rows
end ShielddSecurity.VolumeCandidateCapture857
