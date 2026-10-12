import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0039
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8314 16
def localParent : Nat → Option Row
 | 8314 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 202),[(31052,1)]⟩
 | 8315 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 203),[(31053,1)]⟩
 | 8316 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 204),[(31055,1)]⟩
 | 8317 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 205),[(31054,4),(31055,1)]⟩
 | 8318 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 206),[(31056,1)]⟩
 | 8319 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 207),[(31057,1)]⟩
 | 8320 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 208),[(31059,1)]⟩
 | 8321 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 209),[(31058,4),(31059,1)]⟩
 | 8322 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 210),[(31060,1)]⟩
 | 8323 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 211),[(31061,1)]⟩
 | 8324 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 212),[(31063,1)]⟩
 | 8325 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 213),[(31062,4),(31063,1)]⟩
 | 8326 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 214),[(31064,1)]⟩
 | 8327 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 215),[(31065,1)]⟩
 | 8328 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 216),[(31067,1)]⟩
 | 8329 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 217),[(31066,4),(31067,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B05.count
