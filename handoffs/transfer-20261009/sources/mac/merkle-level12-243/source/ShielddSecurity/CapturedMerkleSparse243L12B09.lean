import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0039
import ShielddSecurity.CapturedArithmetic45B0040
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B09
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 92).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8378 16
def localParent : Nat → Option Row
 | 8378 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 266),[(31116,1)]⟩
 | 8379 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 267),[(31117,1)]⟩
 | 8380 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 268),[(31119,1)]⟩
 | 8381 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 269),[(31118,4),(31119,1)]⟩
 | 8382 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 270),[(31120,1)]⟩
 | 8383 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 271),[(31121,1)]⟩
 | 8384 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 272),[(31123,1)]⟩
 | 8385 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 273),[(31122,4),(31123,1)]⟩
 | 8386 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 274),[(31124,1)]⟩
 | 8387 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 275),[(31125,1)]⟩
 | 8388 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 276),[(31127,1)]⟩
 | 8389 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 277),[(31126,4),(31127,1)]⟩
 | 8390 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 278),[(31128,1)]⟩
 | 8391 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 0),[(31129,1)]⟩
 | 8392 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 1),[(31131,1)]⟩
 | 8393 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 2),[(31130,4),(31131,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B09.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B09.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B09.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B09.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B09.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B09.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B09.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B09.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B09.count
