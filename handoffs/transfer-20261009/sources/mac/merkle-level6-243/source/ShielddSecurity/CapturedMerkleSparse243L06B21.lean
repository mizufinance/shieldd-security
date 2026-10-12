import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0028
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6026 16
def localParent : Nat → Option Row
 | 6026 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 90),[(28764,1)]⟩
 | 6027 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 91),[(28765,1)]⟩
 | 6028 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 92),[(28767,1)]⟩
 | 6029 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 93),[(28766,4),(28767,1)]⟩
 | 6030 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 0),[(28768,1)]⟩
 | 6031 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 1),[(28769,1)]⟩
 | 6032 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 2),[(28771,1)]⟩
 | 6033 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 3),[(28770,4),(28771,1)]⟩
 | 6034 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 4),[(28772,1)]⟩
 | 6035 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 5),[(28773,1)]⟩
 | 6036 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 6),[(28775,1)]⟩
 | 6037 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 7),[(28774,4),(28775,1)]⟩
 | 6038 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 8),[(28776,1)]⟩
 | 6039 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 9),[(28777,1)]⟩
 | 6040 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 10),[(28779,1)]⟩
 | 6041 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 11),[(28778,4),(28779,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B21.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B21.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B21.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B21.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B21.count
