import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0039
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8330 16
def localParent : Nat → Option Row
 | 8330 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 218),[(31068,1)]⟩
 | 8331 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 219),[(31069,1)]⟩
 | 8332 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 220),[(31071,1)]⟩
 | 8333 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 221),[(31070,4),(31071,1)]⟩
 | 8334 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 222),[(31072,1)]⟩
 | 8335 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 223),[(31073,1)]⟩
 | 8336 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 224),[(31075,1)]⟩
 | 8337 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 225),[(31074,4),(31075,1)]⟩
 | 8338 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 226),[(31076,1)]⟩
 | 8339 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 227),[(31077,1)]⟩
 | 8340 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 228),[(31079,1)]⟩
 | 8341 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 229),[(31078,4),(31079,1)]⟩
 | 8342 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 230),[(31080,1)]⟩
 | 8343 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 231),[(31081,1)]⟩
 | 8344 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 232),[(31083,1)]⟩
 | 8345 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 233),[(31082,4),(31083,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B06.count
