import ShielddSecurity.MerkleHash27Whole
import ShielddSecurity.CompilerIndexedCopyStream171
import ShielddSecurity.CapturedFullRelation58
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstGlobal186B01
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := MerkleHash27Whole.selectedRows.drop 16 |>.take 16
def indices : List Nat := List.range' 2750 16
def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length=16 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) : Satisfies rho rows :=
 CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
 ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleFirstGlobal186B01

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B01.rows
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B01.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B01.indices
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B01.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B01.productionCheck
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B01.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B01.checked
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B01.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B01.count
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B01.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstGlobal186B01.sound
#print axioms ShielddSecurity.CapturedMerkleFirstGlobal186B01.sound
