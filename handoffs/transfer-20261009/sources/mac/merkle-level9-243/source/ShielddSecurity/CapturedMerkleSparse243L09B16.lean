import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0034
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7218 16
def localParent : Nat → Option Row
 | 7218 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 48),[(29956,1)]⟩
 | 7219 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 49),[(29957,1)]⟩
 | 7220 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 50),[(29959,1)]⟩
 | 7221 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 51),[(29958,4),(29959,1)]⟩
 | 7222 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 52),[(29960,1)]⟩
 | 7223 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 53),[(29961,1)]⟩
 | 7224 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 54),[(29963,1)]⟩
 | 7225 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 55),[(29962,4),(29963,1)]⟩
 | 7226 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 56),[(29964,1)]⟩
 | 7227 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 57),[(29965,1)]⟩
 | 7228 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 58),[(29967,1)]⟩
 | 7229 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 59),[(29966,4),(29967,1)]⟩
 | 7230 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 60),[(29968,1)]⟩
 | 7231 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 61),[(29969,1)]⟩
 | 7232 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 62),[(29971,1)]⟩
 | 7233 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 63),[(29970,4),(29971,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B16.count
