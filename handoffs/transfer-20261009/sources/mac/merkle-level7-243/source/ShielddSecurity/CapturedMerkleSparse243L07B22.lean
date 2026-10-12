import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 300).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6466 16
def localParent : Nat → Option Row
 | 6466 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 18),[(29204,1)]⟩
 | 6467 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 19),[(29205,1)]⟩
 | 6468 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 20),[(29207,1)]⟩
 | 6469 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 21),[(29206,4),(29207,1)]⟩
 | 6470 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 22),[(29208,1)]⟩
 | 6471 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 23),[(29209,1)]⟩
 | 6472 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 24),[(29211,1)]⟩
 | 6473 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 25),[(29210,4),(29211,1)]⟩
 | 6474 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 26),[(29212,1)]⟩
 | 6475 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 27),[(29213,1)]⟩
 | 6476 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 28),[(29215,1)]⟩
 | 6477 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 29),[(29214,4),(29215,1)]⟩
 | 6478 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 30),[(29216,1)]⟩
 | 6479 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 31),[(29217,1)]⟩
 | 6480 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 32),[(29219,1)]⟩
 | 6481 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 33),[(29218,4),(29219,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B22.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B22.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B22.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B22.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B22.count
