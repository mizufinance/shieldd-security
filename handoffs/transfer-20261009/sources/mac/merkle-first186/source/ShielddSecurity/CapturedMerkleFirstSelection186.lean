import ShielddSecurity.MerkleSelection26Proof
import ShielddSecurity.CompilerIndexedCopyStream171
import ShielddSecurity.CapturedFullRelation58
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstSelection186
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def indices : List Nat := List.range' 2722 12++[200769]
def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices MerkleSelection26Data.originalRows
theorem checked : productionCheck=true := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho MerkleSelection26Data.originalRows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices MerkleSelection26Data.originalRows checked rho
 ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleFirstSelection186

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSelection186.indices
#print axioms ShielddSecurity.CapturedMerkleFirstSelection186.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSelection186.productionCheck
#print axioms ShielddSecurity.CapturedMerkleFirstSelection186.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSelection186.checked
#print axioms ShielddSecurity.CapturedMerkleFirstSelection186.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSelection186.sound
#print axioms ShielddSecurity.CapturedMerkleFirstSelection186.sound
