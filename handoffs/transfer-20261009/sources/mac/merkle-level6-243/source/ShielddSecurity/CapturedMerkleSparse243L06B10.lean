import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5850 16
def localParent : Nat → Option Row
 | 5850 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 236),[(28588,1)]⟩
 | 5851 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 237),[(28589,1)]⟩
 | 5852 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 238),[(28591,1)]⟩
 | 5853 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 239),[(28590,4),(28591,1)]⟩
 | 5854 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 240),[(28592,1)]⟩
 | 5855 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 241),[(28593,1)]⟩
 | 5856 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 242),[(28595,1)]⟩
 | 5857 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 243),[(28594,4),(28595,1)]⟩
 | 5858 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 244),[(28596,1)]⟩
 | 5859 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 245),[(28597,1)]⟩
 | 5860 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 246),[(28599,1)]⟩
 | 5861 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 247),[(28598,4),(28599,1)]⟩
 | 5862 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 248),[(28600,1)]⟩
 | 5863 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 249),[(28601,1)]⟩
 | 5864 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 250),[(28603,1)]⟩
 | 5865 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 251),[(28602,4),(28603,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B10.count
