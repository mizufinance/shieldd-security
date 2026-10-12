import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0030
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6418 16
def localParent : Nat → Option Row
 | 6418 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 70),[(29156,1)]⟩
 | 6419 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 71),[(29157,1)]⟩
 | 6420 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 72),[(29159,1)]⟩
 | 6421 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 73),[(29158,4),(29159,1)]⟩
 | 6422 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 74),[(29160,1)]⟩
 | 6423 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 75),[(29161,1)]⟩
 | 6424 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 76),[(29163,1)]⟩
 | 6425 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 77),[(29162,4),(29163,1)]⟩
 | 6426 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 78),[(29164,1)]⟩
 | 6427 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 79),[(29165,1)]⟩
 | 6428 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 80),[(29167,1)]⟩
 | 6429 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 81),[(29166,4),(29167,1)]⟩
 | 6430 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 82),[(29168,1)]⟩
 | 6431 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 83),[(29169,1)]⟩
 | 6432 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 84),[(29171,1)]⟩
 | 6433 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 85),[(29170,4),(29171,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B19.count
