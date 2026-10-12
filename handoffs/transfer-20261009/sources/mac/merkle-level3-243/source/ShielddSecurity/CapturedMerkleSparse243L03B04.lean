import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0020
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4482 16
def localParent : Nat → Option Row
 | 4482 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 204),[(27220,1)]⟩
 | 4483 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 205),[(27221,1)]⟩
 | 4484 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 206),[(27223,1)]⟩
 | 4485 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 207),[(27222,4),(27223,1)]⟩
 | 4486 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 208),[(27224,1)]⟩
 | 4487 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 209),[(27225,1)]⟩
 | 4488 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 210),[(27227,1)]⟩
 | 4489 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 211),[(27226,4),(27227,1)]⟩
 | 4490 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 212),[(27228,1)]⟩
 | 4491 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 213),[(27229,1)]⟩
 | 4492 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 214),[(27231,1)]⟩
 | 4493 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 215),[(27230,4),(27231,1)]⟩
 | 4494 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 216),[(27232,1)]⟩
 | 4495 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 217),[(27233,1)]⟩
 | 4496 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 218),[(27235,1)]⟩
 | 4497 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 219),[(27234,4),(27235,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B04.count
