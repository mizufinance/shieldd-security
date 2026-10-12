import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6618 16
def localParent : Nat → Option Row
 | 6618 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 170),[(29356,1)]⟩
 | 6619 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 171),[(29357,1)]⟩
 | 6620 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 172),[(29359,1)]⟩
 | 6621 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 173),[(29358,4),(29359,1)]⟩
 | 6622 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 174),[(29360,1)]⟩
 | 6623 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 175),[(29361,1)]⟩
 | 6624 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 176),[(29363,1)]⟩
 | 6625 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 177),[(29362,4),(29363,1)]⟩
 | 6626 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 178),[(29364,1)]⟩
 | 6627 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 179),[(29365,1)]⟩
 | 6628 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 180),[(29367,1)]⟩
 | 6629 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 181),[(29366,4),(29367,1)]⟩
 | 6630 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 182),[(29368,1)]⟩
 | 6631 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 183),[(29369,1)]⟩
 | 6632 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 184),[(29371,1)]⟩
 | 6633 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 185),[(29370,4),(29371,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B05.count
