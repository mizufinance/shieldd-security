import ShielddSecurity.MerkleGlobalBody181
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleWide223Pilot
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := (MerkleGlobalBody181.arithmeticRows 1).drop 352 |>.take 64
def indices : List Nat := List.range' 3922 64
def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length=64 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho rows := CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
 ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleWide223Pilot

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleWide223Pilot.rows
#print axioms ShielddSecurity.CapturedMerkleWide223Pilot.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleWide223Pilot.indices
#print axioms ShielddSecurity.CapturedMerkleWide223Pilot.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleWide223Pilot.productionCheck
#print axioms ShielddSecurity.CapturedMerkleWide223Pilot.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleWide223Pilot.checked
#print axioms ShielddSecurity.CapturedMerkleWide223Pilot.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleWide223Pilot.count
#print axioms ShielddSecurity.CapturedMerkleWide223Pilot.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleWide223Pilot.sound
#print axioms ShielddSecurity.CapturedMerkleWide223Pilot.sound
