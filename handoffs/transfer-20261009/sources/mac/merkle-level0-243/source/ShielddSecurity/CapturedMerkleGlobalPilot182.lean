import ShielddSecurity.MerkleGlobalBody181
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalPilot182
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
noncomputable def rows : List Row := (MerkleGlobalBody181.arithmeticRows 0).take 16
def indices : List Nat := List.range' 3146 16
noncomputable def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy
  CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length=16 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
    Satisfies rho rows := CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
      ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleGlobalPilot182

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalPilot182.rows
#print axioms ShielddSecurity.CapturedMerkleGlobalPilot182.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalPilot182.indices
#print axioms ShielddSecurity.CapturedMerkleGlobalPilot182.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalPilot182.productionCheck
#print axioms ShielddSecurity.CapturedMerkleGlobalPilot182.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalPilot182.checked
#print axioms ShielddSecurity.CapturedMerkleGlobalPilot182.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalPilot182.count
#print axioms ShielddSecurity.CapturedMerkleGlobalPilot182.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalPilot182.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalPilot182.sound
