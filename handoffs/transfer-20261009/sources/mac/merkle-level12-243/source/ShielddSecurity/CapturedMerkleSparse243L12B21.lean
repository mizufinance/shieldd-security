import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0041
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8570 16
def localParent : Nat → Option Row
 | 8570 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 42),[(31308,1)]⟩
 | 8571 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 43),[(31309,1)]⟩
 | 8572 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 44),[(31311,1)]⟩
 | 8573 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 45),[(31310,4),(31311,1)]⟩
 | 8574 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 46),[(31312,1)]⟩
 | 8575 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 47),[(31313,1)]⟩
 | 8576 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 48),[(31315,1)]⟩
 | 8577 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 49),[(31314,4),(31315,1)]⟩
 | 8578 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 50),[(31316,1)]⟩
 | 8579 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 51),[(31317,1)]⟩
 | 8580 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 52),[(31319,1)]⟩
 | 8581 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 53),[(31318,4),(31319,1)]⟩
 | 8582 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 54),[(31320,1)]⟩
 | 8583 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 55),[(31321,1)]⟩
 | 8584 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 56),[(31323,1)]⟩
 | 8585 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 57),[(31322,4),(31323,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B21.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B21.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B21.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B21.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B21.count
