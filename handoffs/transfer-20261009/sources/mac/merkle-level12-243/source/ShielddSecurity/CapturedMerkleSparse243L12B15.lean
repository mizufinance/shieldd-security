import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0040
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8474 16
def localParent : Nat → Option Row
 | 8474 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 83),[(31212,1)]⟩
 | 8475 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 84),[(31213,1)]⟩
 | 8476 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 85),[(31215,1)]⟩
 | 8477 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 86),[(31214,4),(31215,1)]⟩
 | 8478 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 87),[(31216,1)]⟩
 | 8479 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 88),[(31217,1)]⟩
 | 8480 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 89),[(31219,1)]⟩
 | 8481 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 90),[(31218,4),(31219,1)]⟩
 | 8482 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 91),[(31220,1)]⟩
 | 8483 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 92),[(31221,1)]⟩
 | 8484 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 93),[(31223,1)]⟩
 | 8485 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 94),[(31222,4),(31223,1)]⟩
 | 8486 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 95),[(31224,1)]⟩
 | 8487 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 96),[(31225,1)]⟩
 | 8488 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 97),[(31227,1)]⟩
 | 8489 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 98),[(31226,4),(31227,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B15.count
