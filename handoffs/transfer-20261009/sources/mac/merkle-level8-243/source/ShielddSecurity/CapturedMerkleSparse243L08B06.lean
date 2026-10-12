import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6634 16
def localParent : Nat → Option Row
 | 6634 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 186),[(29372,1)]⟩
 | 6635 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 187),[(29373,1)]⟩
 | 6636 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 188),[(29375,1)]⟩
 | 6637 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 189),[(29374,4),(29375,1)]⟩
 | 6638 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 190),[(29376,1)]⟩
 | 6639 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 191),[(29377,1)]⟩
 | 6640 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 192),[(29379,1)]⟩
 | 6641 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 193),[(29378,4),(29379,1)]⟩
 | 6642 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 194),[(29380,1)]⟩
 | 6643 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 195),[(29381,1)]⟩
 | 6644 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 196),[(29383,1)]⟩
 | 6645 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 197),[(29382,4),(29383,1)]⟩
 | 6646 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 198),[(29384,1)]⟩
 | 6647 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 199),[(29385,1)]⟩
 | 6648 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 200),[(29387,1)]⟩
 | 6649 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 201),[(29386,4),(29387,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B06.count
