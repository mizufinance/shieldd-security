import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 316).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6906 16
def localParent : Nat → Option Row
 | 6906 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 42),[(29644,1)]⟩
 | 6907 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 43),[(29645,1)]⟩
 | 6908 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 44),[(29647,1)]⟩
 | 6909 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 45),[(29646,4),(29647,1)]⟩
 | 6910 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 46),[(29648,1)]⟩
 | 6911 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 47),[(29649,1)]⟩
 | 6912 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 48),[(29651,1)]⟩
 | 6913 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 49),[(29650,4),(29651,1)]⟩
 | 6914 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 50),[(29652,1)]⟩
 | 6915 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 51),[(29653,1)]⟩
 | 6916 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 52),[(29655,1)]⟩
 | 6917 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 53),[(29654,4),(29655,1)]⟩
 | 6918 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 54),[(29656,1)]⟩
 | 6919 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 55),[(29657,1)]⟩
 | 6920 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 56),[(29659,1)]⟩
 | 6921 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 57),[(29658,4),(29659,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B23.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B23.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B23.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B23.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B23.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B23.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B23.count
