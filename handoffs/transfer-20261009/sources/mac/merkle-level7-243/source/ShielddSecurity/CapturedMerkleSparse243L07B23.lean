import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 316).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6482 16
def localParent : Nat → Option Row
 | 6482 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 34),[(29220,1)]⟩
 | 6483 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 35),[(29221,1)]⟩
 | 6484 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 36),[(29223,1)]⟩
 | 6485 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 37),[(29222,4),(29223,1)]⟩
 | 6486 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 38),[(29224,1)]⟩
 | 6487 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 39),[(29225,1)]⟩
 | 6488 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 40),[(29227,1)]⟩
 | 6489 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 41),[(29226,4),(29227,1)]⟩
 | 6490 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 42),[(29228,1)]⟩
 | 6491 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 43),[(29229,1)]⟩
 | 6492 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 44),[(29231,1)]⟩
 | 6493 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 45),[(29230,4),(29231,1)]⟩
 | 6494 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 46),[(29232,1)]⟩
 | 6495 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 47),[(29233,1)]⟩
 | 6496 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 48),[(29235,1)]⟩
 | 6497 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 49),[(29234,4),(29235,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B23.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B23.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B23.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B23.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B23.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B23.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B23.count
