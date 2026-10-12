import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0040
import ShielddSecurity.CapturedArithmetic45B0041
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8522 16
def localParent : Nat → Option Row
 | 8522 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 131),[(31260,1)]⟩
 | 8523 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 132),[(31261,1)]⟩
 | 8524 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 133),[(31263,1)]⟩
 | 8525 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 134),[(31262,4),(31263,1)]⟩
 | 8526 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 135),[(31264,1)]⟩
 | 8527 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 136),[(31265,1)]⟩
 | 8528 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 0),[(31267,1)]⟩
 | 8529 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 1),[(31266,4),(31267,1)]⟩
 | 8530 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 2),[(31268,1)]⟩
 | 8531 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 3),[(31269,1)]⟩
 | 8532 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 4),[(31271,1)]⟩
 | 8533 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 5),[(31270,4),(31271,1)]⟩
 | 8534 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 6),[(31272,1)]⟩
 | 8535 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 7),[(31273,1)]⟩
 | 8536 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 8),[(31275,1)]⟩
 | 8537 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 9),[(31274,4),(31275,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B18.count
