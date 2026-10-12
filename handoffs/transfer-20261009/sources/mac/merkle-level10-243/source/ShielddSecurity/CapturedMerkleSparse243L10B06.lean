import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7482 16
def localParent : Nat → Option Row
 | 7482 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 202),[(30220,1)]⟩
 | 7483 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 203),[(30221,1)]⟩
 | 7484 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 204),[(30223,1)]⟩
 | 7485 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 205),[(30222,4),(30223,1)]⟩
 | 7486 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 206),[(30224,1)]⟩
 | 7487 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 207),[(30225,1)]⟩
 | 7488 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 208),[(30227,1)]⟩
 | 7489 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 209),[(30226,4),(30227,1)]⟩
 | 7490 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 210),[(30228,1)]⟩
 | 7491 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 211),[(30229,1)]⟩
 | 7492 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 212),[(30231,1)]⟩
 | 7493 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 213),[(30230,4),(30231,1)]⟩
 | 7494 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 214),[(30232,1)]⟩
 | 7495 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 215),[(30233,1)]⟩
 | 7496 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 216),[(30235,1)]⟩
 | 7497 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 217),[(30234,4),(30235,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B06.count
