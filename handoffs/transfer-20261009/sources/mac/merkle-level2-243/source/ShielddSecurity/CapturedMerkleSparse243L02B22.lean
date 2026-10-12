import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0020
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 300).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4346 16
def localParent : Nat → Option Row
 | 4346 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 68),[(27084,1)]⟩
 | 4347 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 69),[(27085,1)]⟩
 | 4348 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 70),[(27087,1)]⟩
 | 4349 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 71),[(27086,4),(27087,1)]⟩
 | 4350 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 72),[(27088,1)]⟩
 | 4351 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 73),[(27089,1)]⟩
 | 4352 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 74),[(27091,1)]⟩
 | 4353 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 75),[(27090,4),(27091,1)]⟩
 | 4354 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 76),[(27092,1)]⟩
 | 4355 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 77),[(27093,1)]⟩
 | 4356 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 78),[(27095,1)]⟩
 | 4357 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 79),[(27094,4),(27095,1)]⟩
 | 4358 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 80),[(27096,1)]⟩
 | 4359 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 81),[(27097,1)]⟩
 | 4360 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 82),[(27099,1)]⟩
 | 4361 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 83),[(27098,4),(27099,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B22.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B22.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B22.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B22.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B22.count
