import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 316).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7330 16
def localParent : Nat → Option Row
 | 7330 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 50),[(30068,1)]⟩
 | 7331 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 51),[(30069,1)]⟩
 | 7332 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 52),[(30071,1)]⟩
 | 7333 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 53),[(30070,4),(30071,1)]⟩
 | 7334 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 54),[(30072,1)]⟩
 | 7335 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 55),[(30073,1)]⟩
 | 7336 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 56),[(30075,1)]⟩
 | 7337 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 57),[(30074,4),(30075,1)]⟩
 | 7338 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 58),[(30076,1)]⟩
 | 7339 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 59),[(30077,1)]⟩
 | 7340 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 60),[(30079,1)]⟩
 | 7341 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 61),[(30078,4),(30079,1)]⟩
 | 7342 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 62),[(30080,1)]⟩
 | 7343 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 63),[(30081,1)]⟩
 | 7344 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 64),[(30083,1)]⟩
 | 7345 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 65),[(30082,4),(30083,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B23.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B23.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B23.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B23.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B23.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B23.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B23.count
