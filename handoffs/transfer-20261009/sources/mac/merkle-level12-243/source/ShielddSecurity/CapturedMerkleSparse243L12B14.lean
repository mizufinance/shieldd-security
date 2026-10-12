import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0040
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B14
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 172).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8458 16
def localParent : Nat → Option Row
 | 8458 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 67),[(31196,1)]⟩
 | 8459 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 68),[(31197,1)]⟩
 | 8460 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 69),[(31199,1)]⟩
 | 8461 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 70),[(31198,4),(31199,1)]⟩
 | 8462 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 71),[(31200,1)]⟩
 | 8463 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 72),[(31201,1)]⟩
 | 8464 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 73),[(31203,1)]⟩
 | 8465 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 74),[(31202,4),(31203,1)]⟩
 | 8466 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 75),[(31204,1)]⟩
 | 8467 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 76),[(31205,1)]⟩
 | 8468 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 77),[(31207,1)]⟩
 | 8469 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 78),[(31206,4),(31207,1)]⟩
 | 8470 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 79),[(31208,1)]⟩
 | 8471 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 80),[(31209,1)]⟩
 | 8472 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 81),[(31211,1)]⟩
 | 8473 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 82),[(31210,4),(31211,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B14

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B14.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B14.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B14.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B14.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B14.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B14.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B14.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B14.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B14.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B14.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B14.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B14.count
