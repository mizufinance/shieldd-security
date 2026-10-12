import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6090 16
def localParent : Nat → Option Row
 | 6090 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 60),[(28828,1)]⟩
 | 6091 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 61),[(28829,1)]⟩
 | 6092 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 62),[(28831,1)]⟩
 | 6093 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 63),[(28830,4),(28831,1)]⟩
 | 6094 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 64),[(28832,1)]⟩
 | 6095 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 65),[(28833,1)]⟩
 | 6096 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 66),[(28835,1)]⟩
 | 6097 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 67),[(28834,4),(28835,1)]⟩
 | 6098 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 68),[(28836,1)]⟩
 | 6099 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 69),[(28837,1)]⟩
 | 6100 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 70),[(28839,1)]⟩
 | 6101 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 71),[(28838,4),(28839,1)]⟩
 | 6102 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 72),[(28840,1)]⟩
 | 6103 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 73),[(28841,1)]⟩
 | 6104 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 74),[(28843,1)]⟩
 | 6105 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 75),[(28842,4),(28843,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B25.count
