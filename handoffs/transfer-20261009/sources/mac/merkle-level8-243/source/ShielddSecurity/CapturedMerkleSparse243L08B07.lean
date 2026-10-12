import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6650 16
def localParent : Nat → Option Row
 | 6650 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 202),[(29388,1)]⟩
 | 6651 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 203),[(29389,1)]⟩
 | 6652 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 204),[(29391,1)]⟩
 | 6653 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 205),[(29390,4),(29391,1)]⟩
 | 6654 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 206),[(29392,1)]⟩
 | 6655 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 207),[(29393,1)]⟩
 | 6656 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 208),[(29395,1)]⟩
 | 6657 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 209),[(29394,4),(29395,1)]⟩
 | 6658 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 210),[(29396,1)]⟩
 | 6659 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 211),[(29397,1)]⟩
 | 6660 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 212),[(29399,1)]⟩
 | 6661 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 213),[(29398,4),(29399,1)]⟩
 | 6662 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 214),[(29400,1)]⟩
 | 6663 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 215),[(29401,1)]⟩
 | 6664 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 216),[(29403,1)]⟩
 | 6665 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 217),[(29402,4),(29403,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B07.count
