import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0030
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6354 16
def localParent : Nat → Option Row
 | 6354 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 6),[(29092,1)]⟩
 | 6355 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 7),[(29093,1)]⟩
 | 6356 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 8),[(29095,1)]⟩
 | 6357 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 9),[(29094,4),(29095,1)]⟩
 | 6358 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 10),[(29096,1)]⟩
 | 6359 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 11),[(29097,1)]⟩
 | 6360 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 12),[(29099,1)]⟩
 | 6361 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 13),[(29098,4),(29099,1)]⟩
 | 6362 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 14),[(29100,1)]⟩
 | 6363 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 15),[(29101,1)]⟩
 | 6364 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 16),[(29103,1)]⟩
 | 6365 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 17),[(29102,4),(29103,1)]⟩
 | 6366 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 18),[(29104,1)]⟩
 | 6367 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 19),[(29105,1)]⟩
 | 6368 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 20),[(29107,1)]⟩
 | 6369 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 21),[(29106,4),(29107,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B15.count
