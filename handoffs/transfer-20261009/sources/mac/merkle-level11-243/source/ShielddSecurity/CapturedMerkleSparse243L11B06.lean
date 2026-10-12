import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7906 16
def localParent : Nat → Option Row
 | 7906 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 210),[(30644,1)]⟩
 | 7907 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 211),[(30645,1)]⟩
 | 7908 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 212),[(30647,1)]⟩
 | 7909 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 213),[(30646,4),(30647,1)]⟩
 | 7910 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 214),[(30648,1)]⟩
 | 7911 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 215),[(30649,1)]⟩
 | 7912 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 216),[(30651,1)]⟩
 | 7913 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 217),[(30650,4),(30651,1)]⟩
 | 7914 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 218),[(30652,1)]⟩
 | 7915 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 219),[(30653,1)]⟩
 | 7916 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 220),[(30655,1)]⟩
 | 7917 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 221),[(30654,4),(30655,1)]⟩
 | 7918 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 222),[(30656,1)]⟩
 | 7919 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 223),[(30657,1)]⟩
 | 7920 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 224),[(30659,1)]⟩
 | 7921 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 225),[(30658,4),(30659,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B06.count
