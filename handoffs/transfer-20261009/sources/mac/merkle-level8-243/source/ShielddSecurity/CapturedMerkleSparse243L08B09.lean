import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B09
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 92).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6682 16
def localParent : Nat → Option Row
 | 6682 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 234),[(29420,1)]⟩
 | 6683 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 235),[(29421,1)]⟩
 | 6684 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 236),[(29423,1)]⟩
 | 6685 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 237),[(29422,4),(29423,1)]⟩
 | 6686 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 238),[(29424,1)]⟩
 | 6687 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 239),[(29425,1)]⟩
 | 6688 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 240),[(29427,1)]⟩
 | 6689 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 241),[(29426,4),(29427,1)]⟩
 | 6690 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 242),[(29428,1)]⟩
 | 6691 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 243),[(29429,1)]⟩
 | 6692 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 244),[(29431,1)]⟩
 | 6693 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 245),[(29430,4),(29431,1)]⟩
 | 6694 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 246),[(29432,1)]⟩
 | 6695 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 247),[(29433,1)]⟩
 | 6696 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 248),[(29435,1)]⟩
 | 6697 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 249),[(29434,4),(29435,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B09.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B09.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B09.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B09.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B09.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B09.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B09.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B09.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B09.count
