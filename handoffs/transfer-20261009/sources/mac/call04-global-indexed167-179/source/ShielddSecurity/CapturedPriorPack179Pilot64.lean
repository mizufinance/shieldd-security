import ShielddSecurity.CompilerIndexedCopyConstant178
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CapturedInitial73419Completion01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedPriorPack179Pilot64
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def rows : List Row := (CapturedPriorRows16Chunk01.rows.drop 0).take 64
def indices : List Nat := List.range' 0 64
noncomputable def productionCheck : Bool := CompilerIndexedCopyConstant178.check copy
  CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length=64 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho rows :=
  CompilerIndexedCopyConstant178.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
    ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedPriorPack179Pilot64

set_option pp.all true in
#check @ShielddSecurity.CapturedPriorPack179Pilot64.rows
#print axioms ShielddSecurity.CapturedPriorPack179Pilot64.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedPriorPack179Pilot64.indices
#print axioms ShielddSecurity.CapturedPriorPack179Pilot64.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedPriorPack179Pilot64.productionCheck
#print axioms ShielddSecurity.CapturedPriorPack179Pilot64.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedPriorPack179Pilot64.checked
#print axioms ShielddSecurity.CapturedPriorPack179Pilot64.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedPriorPack179Pilot64.count
#print axioms ShielddSecurity.CapturedPriorPack179Pilot64.count
set_option pp.all true in
#check @ShielddSecurity.CapturedPriorPack179Pilot64.sound
#print axioms ShielddSecurity.CapturedPriorPack179Pilot64.sound
