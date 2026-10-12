import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0042
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8850 16
def localParent : Nat → Option Row
 | 8850 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 60),[(31588,1)]⟩
 | 8851 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 61),[(31589,1)]⟩
 | 8852 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 62),[(31591,1)]⟩
 | 8853 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 63),[(31590,4),(31591,1)]⟩
 | 8854 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 64),[(31592,1)]⟩
 | 8855 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 65),[(31593,1)]⟩
 | 8856 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 66),[(31595,1)]⟩
 | 8857 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 67),[(31594,4),(31595,1)]⟩
 | 8858 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 68),[(31596,1)]⟩
 | 8859 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 69),[(31597,1)]⟩
 | 8860 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 70),[(31599,1)]⟩
 | 8861 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 71),[(31598,4),(31599,1)]⟩
 | 8862 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 72),[(31600,1)]⟩
 | 8863 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 73),[(31601,1)]⟩
 | 8864 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 74),[(31603,1)]⟩
 | 8865 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 75),[(31602,4),(31603,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B12.count
