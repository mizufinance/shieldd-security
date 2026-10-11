import ShielddSecurity.CompilerIndexedCopySelection166
import ShielddSecurity.CapturedFullRelation58
import ShielddSecurity.CapturedInitial73419Completion01
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedCall04GlobalBinding167Pilot
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
noncomputable def rows : List Row := CapturedInitial73419Completion01.callRows.take 32
def indices : List Nat := List.range' 322 32
noncomputable def productionCheck : Bool := CompilerIndexedCopySelection166.check p copy
  CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length=32 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho rows :=
  CompilerIndexedCopySelection166.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
    ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedCall04GlobalBinding167Pilot

set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding167Pilot.rows
#print axioms ShielddSecurity.CapturedCall04GlobalBinding167Pilot.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding167Pilot.indices
#print axioms ShielddSecurity.CapturedCall04GlobalBinding167Pilot.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding167Pilot.productionCheck
#print axioms ShielddSecurity.CapturedCall04GlobalBinding167Pilot.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding167Pilot.checked
#print axioms ShielddSecurity.CapturedCall04GlobalBinding167Pilot.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding167Pilot.count
#print axioms ShielddSecurity.CapturedCall04GlobalBinding167Pilot.count
set_option pp.all true in
#check @ShielddSecurity.CapturedCall04GlobalBinding167Pilot.sound
#print axioms ShielddSecurity.CapturedCall04GlobalBinding167Pilot.sound
