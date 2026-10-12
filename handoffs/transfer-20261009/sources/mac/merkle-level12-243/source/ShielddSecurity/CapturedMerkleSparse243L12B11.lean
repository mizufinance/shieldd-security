import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0040
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8410 16
def localParent : Nat → Option Row
 | 8410 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 19),[(31148,1)]⟩
 | 8411 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 20),[(31149,1)]⟩
 | 8412 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 21),[(31151,1)]⟩
 | 8413 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 22),[(31150,4),(31151,1)]⟩
 | 8414 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 23),[(31152,1)]⟩
 | 8415 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 24),[(31153,1)]⟩
 | 8416 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 25),[(31155,1)]⟩
 | 8417 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 26),[(31154,4),(31155,1)]⟩
 | 8418 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 27),[(31156,1)]⟩
 | 8419 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 28),[(31157,1)]⟩
 | 8420 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 29),[(31159,1)]⟩
 | 8421 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 30),[(31158,4),(31159,1)]⟩
 | 8422 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 31),[(31160,1)]⟩
 | 8423 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 32),[(31161,1)]⟩
 | 8424 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 33),[(31163,1)]⟩
 | 8425 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 34),[(31162,4),(31163,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B11.count
