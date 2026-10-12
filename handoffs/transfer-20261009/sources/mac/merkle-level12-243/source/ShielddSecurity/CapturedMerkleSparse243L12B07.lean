import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0039
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8346 16
def localParent : Nat → Option Row
 | 8346 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 234),[(31084,1)]⟩
 | 8347 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 235),[(31085,1)]⟩
 | 8348 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 236),[(31087,1)]⟩
 | 8349 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 237),[(31086,4),(31087,1)]⟩
 | 8350 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 238),[(31088,1)]⟩
 | 8351 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 239),[(31089,1)]⟩
 | 8352 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 240),[(31091,1)]⟩
 | 8353 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 241),[(31090,4),(31091,1)]⟩
 | 8354 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 242),[(31092,1)]⟩
 | 8355 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 243),[(31093,1)]⟩
 | 8356 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 244),[(31095,1)]⟩
 | 8357 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 245),[(31094,4),(31095,1)]⟩
 | 8358 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 246),[(31096,1)]⟩
 | 8359 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 247),[(31097,1)]⟩
 | 8360 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 248),[(31099,1)]⟩
 | 8361 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 249),[(31098,4),(31099,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B07.count
