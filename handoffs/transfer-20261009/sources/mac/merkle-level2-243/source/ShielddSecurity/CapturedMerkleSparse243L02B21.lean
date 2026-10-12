import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0020
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4330 16
def localParent : Nat → Option Row
 | 4330 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 52),[(27068,1)]⟩
 | 4331 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 53),[(27069,1)]⟩
 | 4332 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 54),[(27071,1)]⟩
 | 4333 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 55),[(27070,4),(27071,1)]⟩
 | 4334 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 56),[(27072,1)]⟩
 | 4335 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 57),[(27073,1)]⟩
 | 4336 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 58),[(27075,1)]⟩
 | 4337 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 59),[(27074,4),(27075,1)]⟩
 | 4338 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 60),[(27076,1)]⟩
 | 4339 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 61),[(27077,1)]⟩
 | 4340 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 62),[(27079,1)]⟩
 | 4341 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 63),[(27078,4),(27079,1)]⟩
 | 4342 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 64),[(27080,1)]⟩
 | 4343 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 65),[(27081,1)]⟩
 | 4344 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 66),[(27083,1)]⟩
 | 4345 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 67),[(27082,4),(27083,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B21.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B21.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B21.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B21.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B21.count
