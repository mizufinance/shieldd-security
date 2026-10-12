import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0020
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 316).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4362 16
def localParent : Nat → Option Row
 | 4362 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 84),[(27100,1)]⟩
 | 4363 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 85),[(27101,1)]⟩
 | 4364 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 86),[(27103,1)]⟩
 | 4365 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 87),[(27102,4),(27103,1)]⟩
 | 4366 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 88),[(27104,1)]⟩
 | 4367 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 89),[(27105,1)]⟩
 | 4368 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 90),[(27107,1)]⟩
 | 4369 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 91),[(27106,4),(27107,1)]⟩
 | 4370 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 92),[(27108,1)]⟩
 | 4371 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 93),[(27109,1)]⟩
 | 4372 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 94),[(27111,1)]⟩
 | 4373 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 95),[(27110,4),(27111,1)]⟩
 | 4374 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 96),[(27112,1)]⟩
 | 4375 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 97),[(27113,1)]⟩
 | 4376 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 98),[(27115,1)]⟩
 | 4377 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 99),[(27114,4),(27115,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B23.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B23.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B23.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B23.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B23.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B23.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B23.count
