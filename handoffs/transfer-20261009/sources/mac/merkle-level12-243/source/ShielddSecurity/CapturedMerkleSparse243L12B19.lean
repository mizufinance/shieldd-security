import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0041
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8538 16
def localParent : Nat → Option Row
 | 8538 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 10),[(31276,1)]⟩
 | 8539 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 11),[(31277,1)]⟩
 | 8540 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 12),[(31279,1)]⟩
 | 8541 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 13),[(31278,4),(31279,1)]⟩
 | 8542 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 14),[(31280,1)]⟩
 | 8543 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 15),[(31281,1)]⟩
 | 8544 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 16),[(31283,1)]⟩
 | 8545 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 17),[(31282,4),(31283,1)]⟩
 | 8546 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 18),[(31284,1)]⟩
 | 8547 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 19),[(31285,1)]⟩
 | 8548 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 20),[(31287,1)]⟩
 | 8549 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 21),[(31286,4),(31287,1)]⟩
 | 8550 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 22),[(31288,1)]⟩
 | 8551 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 23),[(31289,1)]⟩
 | 8552 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 24),[(31291,1)]⟩
 | 8553 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 25),[(31290,4),(31291,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B19.count
