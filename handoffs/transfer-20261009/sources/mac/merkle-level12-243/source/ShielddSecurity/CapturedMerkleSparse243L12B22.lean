import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0041
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 300).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8586 16
def localParent : Nat → Option Row
 | 8586 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 58),[(31324,1)]⟩
 | 8587 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 59),[(31325,1)]⟩
 | 8588 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 60),[(31327,1)]⟩
 | 8589 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 61),[(31326,4),(31327,1)]⟩
 | 8590 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 62),[(31328,1)]⟩
 | 8591 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 63),[(31329,1)]⟩
 | 8592 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 64),[(31331,1)]⟩
 | 8593 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 65),[(31330,4),(31331,1)]⟩
 | 8594 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 66),[(31332,1)]⟩
 | 8595 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 67),[(31333,1)]⟩
 | 8596 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 68),[(31335,1)]⟩
 | 8597 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 69),[(31334,4),(31335,1)]⟩
 | 8598 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 70),[(31336,1)]⟩
 | 8599 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 71),[(31337,1)]⟩
 | 8600 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 72),[(31339,1)]⟩
 | 8601 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 73),[(31338,4),(31339,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B22.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B22.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B22.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B22.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B22.count
