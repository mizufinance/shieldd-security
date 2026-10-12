import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7298 16
def localParent : Nat → Option Row
 | 7298 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 18),[(30036,1)]⟩
 | 7299 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 19),[(30037,1)]⟩
 | 7300 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 20),[(30039,1)]⟩
 | 7301 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 21),[(30038,4),(30039,1)]⟩
 | 7302 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 22),[(30040,1)]⟩
 | 7303 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 23),[(30041,1)]⟩
 | 7304 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 24),[(30043,1)]⟩
 | 7305 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 25),[(30042,4),(30043,1)]⟩
 | 7306 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 26),[(30044,1)]⟩
 | 7307 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 27),[(30045,1)]⟩
 | 7308 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 28),[(30047,1)]⟩
 | 7309 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 29),[(30046,4),(30047,1)]⟩
 | 7310 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 30),[(30048,1)]⟩
 | 7311 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 31),[(30049,1)]⟩
 | 7312 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 32),[(30051,1)]⟩
 | 7313 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 33),[(30050,4),(30051,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B21.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B21.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B21.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B21.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B21.count
