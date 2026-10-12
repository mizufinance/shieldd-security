import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 300).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6042 16
def localParent : Nat → Option Row
 | 6042 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 12),[(28780,1)]⟩
 | 6043 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 13),[(28781,1)]⟩
 | 6044 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 14),[(28783,1)]⟩
 | 6045 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 15),[(28782,4),(28783,1)]⟩
 | 6046 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 16),[(28784,1)]⟩
 | 6047 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 17),[(28785,1)]⟩
 | 6048 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 18),[(28787,1)]⟩
 | 6049 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 19),[(28786,4),(28787,1)]⟩
 | 6050 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 20),[(28788,1)]⟩
 | 6051 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 21),[(28789,1)]⟩
 | 6052 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 22),[(28791,1)]⟩
 | 6053 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 23),[(28790,4),(28791,1)]⟩
 | 6054 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 24),[(28792,1)]⟩
 | 6055 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 25),[(28793,1)]⟩
 | 6056 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 26),[(28795,1)]⟩
 | 6057 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 27),[(28794,4),(28795,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B22.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B22.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B22.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B22.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B22.count
