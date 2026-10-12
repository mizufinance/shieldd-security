import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0041
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8618 16
def localParent : Nat → Option Row
 | 8618 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 90),[(31356,1)]⟩
 | 8619 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 91),[(31357,1)]⟩
 | 8620 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 92),[(31359,1)]⟩
 | 8621 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 93),[(31358,4),(31359,1)]⟩
 | 8622 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 94),[(31360,1)]⟩
 | 8623 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 95),[(31361,1)]⟩
 | 8624 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 96),[(31363,1)]⟩
 | 8625 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 97),[(31362,4),(31363,1)]⟩
 | 8626 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 98),[(31364,1)]⟩
 | 8627 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 99),[(31365,1)]⟩
 | 8628 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 100),[(31367,1)]⟩
 | 8629 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 101),[(31366,4),(31367,1)]⟩
 | 8630 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 102),[(31368,1)]⟩
 | 8631 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 103),[(31369,1)]⟩
 | 8632 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 104),[(31371,1)]⟩
 | 8633 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 105),[(31370,4),(31371,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B24.count
