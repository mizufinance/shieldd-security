import ShielddSecurity.CompilerIndexedCopyStream171
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CapturedInitial73419Completion01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedCall04GlobalBinding168F00
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def rows : List Row := (CapturedInitial73419Completion01.callRows.drop 288).take 8
def indices : List Nat := List.range' 610 8
noncomputable def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy
  CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length=8 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho rows :=
  CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
    ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedCall04GlobalBinding168F00

set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding168F00.rows
#print axioms ShielddSecurity.CapturedCall04GlobalBinding168F00.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding168F00.indices
#print axioms ShielddSecurity.CapturedCall04GlobalBinding168F00.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding168F00.productionCheck
#print axioms ShielddSecurity.CapturedCall04GlobalBinding168F00.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding168F00.checked
#print axioms ShielddSecurity.CapturedCall04GlobalBinding168F00.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding168F00.count
#print axioms ShielddSecurity.CapturedCall04GlobalBinding168F00.count
set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding168F00.sound
#print axioms ShielddSecurity.CapturedCall04GlobalBinding168F00.sound
