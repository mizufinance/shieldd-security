import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0039
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8298 16
def localParent : Nat → Option Row
 | 8298 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 186),[(31036,1)]⟩
 | 8299 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 187),[(31037,1)]⟩
 | 8300 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 188),[(31039,1)]⟩
 | 8301 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 189),[(31038,4),(31039,1)]⟩
 | 8302 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 190),[(31040,1)]⟩
 | 8303 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 191),[(31041,1)]⟩
 | 8304 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 192),[(31043,1)]⟩
 | 8305 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 193),[(31042,4),(31043,1)]⟩
 | 8306 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 194),[(31044,1)]⟩
 | 8307 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 195),[(31045,1)]⟩
 | 8308 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 196),[(31047,1)]⟩
 | 8309 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 197),[(31046,4),(31047,1)]⟩
 | 8310 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 198),[(31048,1)]⟩
 | 8311 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 199),[(31049,1)]⟩
 | 8312 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 200),[(31051,1)]⟩
 | 8313 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 201),[(31050,4),(31051,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B04.count
