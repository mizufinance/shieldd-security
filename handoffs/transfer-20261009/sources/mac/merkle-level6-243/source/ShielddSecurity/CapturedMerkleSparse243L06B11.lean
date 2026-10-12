import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5866 16
def localParent : Nat → Option Row
 | 5866 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 252),[(28604,1)]⟩
 | 5867 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 253),[(28605,1)]⟩
 | 5868 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 254),[(28607,1)]⟩
 | 5869 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 255),[(28606,4),(28607,1)]⟩
 | 5870 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 256),[(28608,1)]⟩
 | 5871 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 257),[(28609,1)]⟩
 | 5872 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 258),[(28611,1)]⟩
 | 5873 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 259),[(28610,4),(28611,1)]⟩
 | 5874 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 260),[(28612,1)]⟩
 | 5875 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 261),[(28613,1)]⟩
 | 5876 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 262),[(28615,1)]⟩
 | 5877 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 263),[(28614,4),(28615,1)]⟩
 | 5878 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 264),[(28616,1)]⟩
 | 5879 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 265),[(28617,1)]⟩
 | 5880 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 266),[(28619,1)]⟩
 | 5881 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 267),[(28618,4),(28619,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B11.count
