import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6922 16
def localParent : Nat → Option Row
 | 6922 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 58),[(29660,1)]⟩
 | 6923 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 59),[(29661,1)]⟩
 | 6924 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 60),[(29663,1)]⟩
 | 6925 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 61),[(29662,4),(29663,1)]⟩
 | 6926 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 62),[(29664,1)]⟩
 | 6927 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 63),[(29665,1)]⟩
 | 6928 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 64),[(29667,1)]⟩
 | 6929 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 65),[(29666,4),(29667,1)]⟩
 | 6930 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 66),[(29668,1)]⟩
 | 6931 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 67),[(29669,1)]⟩
 | 6932 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 68),[(29671,1)]⟩
 | 6933 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 69),[(29670,4),(29671,1)]⟩
 | 6934 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 70),[(29672,1)]⟩
 | 6935 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 71),[(29673,1)]⟩
 | 6936 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 72),[(29675,1)]⟩
 | 6937 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 73),[(29674,4),(29675,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B24.count
