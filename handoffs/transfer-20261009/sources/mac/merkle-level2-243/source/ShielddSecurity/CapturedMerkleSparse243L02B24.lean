import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0020
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4378 16
def localParent : Nat → Option Row
 | 4378 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 100),[(27116,1)]⟩
 | 4379 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 101),[(27117,1)]⟩
 | 4380 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 102),[(27119,1)]⟩
 | 4381 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 103),[(27118,4),(27119,1)]⟩
 | 4382 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 104),[(27120,1)]⟩
 | 4383 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 105),[(27121,1)]⟩
 | 4384 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 106),[(27123,1)]⟩
 | 4385 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 107),[(27122,4),(27123,1)]⟩
 | 4386 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 108),[(27124,1)]⟩
 | 4387 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 109),[(27125,1)]⟩
 | 4388 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 110),[(27127,1)]⟩
 | 4389 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 111),[(27126,4),(27127,1)]⟩
 | 4390 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 112),[(27128,1)]⟩
 | 4391 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 113),[(27129,1)]⟩
 | 4392 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 114),[(27131,1)]⟩
 | 4393 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 115),[(27130,4),(27131,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B24.count
