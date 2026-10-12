import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0040
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8426 16
def localParent : Nat → Option Row
 | 8426 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 35),[(31164,1)]⟩
 | 8427 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 36),[(31165,1)]⟩
 | 8428 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 37),[(31167,1)]⟩
 | 8429 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 38),[(31166,4),(31167,1)]⟩
 | 8430 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 39),[(31168,1)]⟩
 | 8431 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 40),[(31169,1)]⟩
 | 8432 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 41),[(31171,1)]⟩
 | 8433 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 42),[(31170,4),(31171,1)]⟩
 | 8434 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 43),[(31172,1)]⟩
 | 8435 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 44),[(31173,1)]⟩
 | 8436 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 45),[(31175,1)]⟩
 | 8437 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 46),[(31174,4),(31175,1)]⟩
 | 8438 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 47),[(31176,1)]⟩
 | 8439 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 48),[(31177,1)]⟩
 | 8440 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 49),[(31179,1)]⟩
 | 8441 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 50),[(31178,4),(31179,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B12.count
