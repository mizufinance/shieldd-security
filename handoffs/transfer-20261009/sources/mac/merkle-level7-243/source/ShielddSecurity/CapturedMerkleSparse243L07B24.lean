import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6498 16
def localParent : Nat → Option Row
 | 6498 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 50),[(29236,1)]⟩
 | 6499 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 51),[(29237,1)]⟩
 | 6500 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 52),[(29239,1)]⟩
 | 6501 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 53),[(29238,4),(29239,1)]⟩
 | 6502 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 54),[(29240,1)]⟩
 | 6503 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 55),[(29241,1)]⟩
 | 6504 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 56),[(29243,1)]⟩
 | 6505 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 57),[(29242,4),(29243,1)]⟩
 | 6506 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 58),[(29244,1)]⟩
 | 6507 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 59),[(29245,1)]⟩
 | 6508 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 60),[(29247,1)]⟩
 | 6509 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 61),[(29246,4),(29247,1)]⟩
 | 6510 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 62),[(29248,1)]⟩
 | 6511 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 63),[(29249,1)]⟩
 | 6512 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 64),[(29251,1)]⟩
 | 6513 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 65),[(29250,4),(29251,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B24.count
