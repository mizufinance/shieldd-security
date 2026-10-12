import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6450 16
def localParent : Nat → Option Row
 | 6450 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 2),[(29188,1)]⟩
 | 6451 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 3),[(29189,1)]⟩
 | 6452 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 4),[(29191,1)]⟩
 | 6453 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 5),[(29190,4),(29191,1)]⟩
 | 6454 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 6),[(29192,1)]⟩
 | 6455 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 7),[(29193,1)]⟩
 | 6456 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 8),[(29195,1)]⟩
 | 6457 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 9),[(29194,4),(29195,1)]⟩
 | 6458 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 10),[(29196,1)]⟩
 | 6459 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 11),[(29197,1)]⟩
 | 6460 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 12),[(29199,1)]⟩
 | 6461 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 13),[(29198,4),(29199,1)]⟩
 | 6462 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 14),[(29200,1)]⟩
 | 6463 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 15),[(29201,1)]⟩
 | 6464 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 16),[(29203,1)]⟩
 | 6465 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 17),[(29202,4),(29203,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B21.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B21.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B21.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B21.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B21.count
