import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B08
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 76).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5818 16
def localParent : Nat → Option Row
 | 5818 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 204),[(28556,1)]⟩
 | 5819 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 205),[(28557,1)]⟩
 | 5820 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 206),[(28559,1)]⟩
 | 5821 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 207),[(28558,4),(28559,1)]⟩
 | 5822 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 208),[(28560,1)]⟩
 | 5823 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 209),[(28561,1)]⟩
 | 5824 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 210),[(28563,1)]⟩
 | 5825 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 211),[(28562,4),(28563,1)]⟩
 | 5826 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 212),[(28564,1)]⟩
 | 5827 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 213),[(28565,1)]⟩
 | 5828 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 214),[(28567,1)]⟩
 | 5829 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 215),[(28566,4),(28567,1)]⟩
 | 5830 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 216),[(28568,1)]⟩
 | 5831 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 217),[(28569,1)]⟩
 | 5832 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 218),[(28571,1)]⟩
 | 5833 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 219),[(28570,4),(28571,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B08

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B08.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B08.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B08.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B08.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B08.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B08.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B08.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B08.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B08.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B08.count
