import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7362 16
def localParent : Nat → Option Row
 | 7362 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 82),[(30100,1)]⟩
 | 7363 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 83),[(30101,1)]⟩
 | 7364 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 84),[(30103,1)]⟩
 | 7365 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 85),[(30102,4),(30103,1)]⟩
 | 7366 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 86),[(30104,1)]⟩
 | 7367 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 87),[(30105,1)]⟩
 | 7368 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 88),[(30107,1)]⟩
 | 7369 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 89),[(30106,4),(30107,1)]⟩
 | 7370 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 90),[(30108,1)]⟩
 | 7371 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 91),[(30109,1)]⟩
 | 7372 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 92),[(30111,1)]⟩
 | 7373 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 93),[(30110,4),(30111,1)]⟩
 | 7374 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 94),[(30112,1)]⟩
 | 7375 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 95),[(30113,1)]⟩
 | 7376 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 96),[(30115,1)]⟩
 | 7377 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 97),[(30114,4),(30115,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B25.count
