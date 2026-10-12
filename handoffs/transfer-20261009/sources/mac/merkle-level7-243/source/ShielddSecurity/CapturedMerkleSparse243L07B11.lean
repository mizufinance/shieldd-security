import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6290 16
def localParent : Nat → Option Row
 | 6290 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 260),[(29028,1)]⟩
 | 6291 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 261),[(29029,1)]⟩
 | 6292 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 262),[(29031,1)]⟩
 | 6293 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 263),[(29030,4),(29031,1)]⟩
 | 6294 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 264),[(29032,1)]⟩
 | 6295 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 265),[(29033,1)]⟩
 | 6296 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 266),[(29035,1)]⟩
 | 6297 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 267),[(29034,4),(29035,1)]⟩
 | 6298 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 268),[(29036,1)]⟩
 | 6299 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 269),[(29037,1)]⟩
 | 6300 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 270),[(29039,1)]⟩
 | 6301 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 271),[(29038,4),(29039,1)]⟩
 | 6302 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 272),[(29040,1)]⟩
 | 6303 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 273),[(29041,1)]⟩
 | 6304 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 274),[(29043,1)]⟩
 | 6305 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 275),[(29042,4),(29043,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B11.count
