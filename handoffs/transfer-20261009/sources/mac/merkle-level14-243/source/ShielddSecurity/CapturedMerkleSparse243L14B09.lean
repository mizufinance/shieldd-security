import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0044
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B09
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 92).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9226 16
def localParent : Nat → Option Row
 | 9226 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 50),[(31964,1)]⟩
 | 9227 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 51),[(31965,1)]⟩
 | 9228 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 52),[(31967,1)]⟩
 | 9229 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 53),[(31966,4),(31967,1)]⟩
 | 9230 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 54),[(31968,1)]⟩
 | 9231 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 55),[(31969,1)]⟩
 | 9232 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 56),[(31971,1)]⟩
 | 9233 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 57),[(31970,4),(31971,1)]⟩
 | 9234 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 58),[(31972,1)]⟩
 | 9235 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 59),[(31973,1)]⟩
 | 9236 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 60),[(31975,1)]⟩
 | 9237 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 61),[(31974,4),(31975,1)]⟩
 | 9238 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 62),[(31976,1)]⟩
 | 9239 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 63),[(31977,1)]⟩
 | 9240 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 64),[(31979,1)]⟩
 | 9241 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 65),[(31978,4),(31979,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B09.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B09.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B09.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B09.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B09.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B09.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B09.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B09.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B09.count
