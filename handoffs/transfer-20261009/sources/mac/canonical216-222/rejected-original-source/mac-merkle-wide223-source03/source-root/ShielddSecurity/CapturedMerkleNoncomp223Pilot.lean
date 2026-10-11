import ShielddSecurity.MerkleGlobalBody181
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleNoncomp223Pilot
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
noncomputable def rows : List Row := (MerkleGlobalBody181.arithmeticRows 1).drop 320 |>.take 64
noncomputable def indices : List Nat := List.range' 3890 64
noncomputable def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length=64 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho rows := CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
 ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleNoncomp223Pilot

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleNoncomp223Pilot.rows
#print axioms ShielddSecurity.CapturedMerkleNoncomp223Pilot.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleNoncomp223Pilot.indices
#print axioms ShielddSecurity.CapturedMerkleNoncomp223Pilot.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleNoncomp223Pilot.productionCheck
#print axioms ShielddSecurity.CapturedMerkleNoncomp223Pilot.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleNoncomp223Pilot.checked
#print axioms ShielddSecurity.CapturedMerkleNoncomp223Pilot.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleNoncomp223Pilot.count
#print axioms ShielddSecurity.CapturedMerkleNoncomp223Pilot.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleNoncomp223Pilot.sound
#print axioms ShielddSecurity.CapturedMerkleNoncomp223Pilot.sound
