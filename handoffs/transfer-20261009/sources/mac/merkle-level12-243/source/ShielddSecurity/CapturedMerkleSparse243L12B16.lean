import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0040
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8490 16
def localParent : Nat → Option Row
 | 8490 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 99),[(31228,1)]⟩
 | 8491 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 100),[(31229,1)]⟩
 | 8492 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 101),[(31231,1)]⟩
 | 8493 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 102),[(31230,4),(31231,1)]⟩
 | 8494 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 103),[(31232,1)]⟩
 | 8495 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 104),[(31233,1)]⟩
 | 8496 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 105),[(31235,1)]⟩
 | 8497 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 106),[(31234,4),(31235,1)]⟩
 | 8498 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 107),[(31236,1)]⟩
 | 8499 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 108),[(31237,1)]⟩
 | 8500 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 109),[(31239,1)]⟩
 | 8501 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 110),[(31238,4),(31239,1)]⟩
 | 8502 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 111),[(31240,1)]⟩
 | 8503 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 112),[(31241,1)]⟩
 | 8504 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 113),[(31243,1)]⟩
 | 8505 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 114),[(31242,4),(31243,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B16.count
