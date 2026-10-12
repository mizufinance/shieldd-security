import ShielddSecurity.MerkleGlobalBody181
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := (MerkleGlobalBody181.arithmeticRows 4).drop 32 |>.take 16
def indices : List Nat := List.range' 4874 16
def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by decide +kernel
theorem count : rows.length=16 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho rows := CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
 ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02.rows
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02.indices
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02.productionCheck
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02.checked
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02.count
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02.sound
#print axioms ShielddSecurity.CapturedMerkleGlobalArithmetic184L04B02.sound
