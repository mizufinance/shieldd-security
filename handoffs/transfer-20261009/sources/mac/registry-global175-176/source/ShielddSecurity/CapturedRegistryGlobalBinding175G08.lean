import ShielddSecurity.CompilerIndexedCopyConstant178
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.RegistryWhole23
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegistryGlobalBinding175G08
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def rows : List Row := (RegistryWhole23.selectedRows.drop 128).take 16
def indices : List Nat := List.range' 2434 16
noncomputable def productionCheck : Bool := CompilerIndexedCopyConstant178.check copy
  CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length=16 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho rows :=
  CompilerIndexedCopyConstant178.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
    ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedRegistryGlobalBinding175G08

set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G08.rows
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G08.indices
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G08.productionCheck
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G08.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G08.checked
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G08.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G08.count
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G08.count
set_option pp.all true in
#check @ShielddSecurity.CapturedRegistryGlobalBinding175G08.sound
#print axioms ShielddSecurity.CapturedRegistryGlobalBinding175G08.sound
