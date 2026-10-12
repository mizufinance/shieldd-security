import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0042
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8834 16
def localParent : Nat → Option Row
 | 8834 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 44),[(31572,1)]⟩
 | 8835 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 45),[(31573,1)]⟩
 | 8836 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 46),[(31575,1)]⟩
 | 8837 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 47),[(31574,4),(31575,1)]⟩
 | 8838 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 48),[(31576,1)]⟩
 | 8839 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 49),[(31577,1)]⟩
 | 8840 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 50),[(31579,1)]⟩
 | 8841 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 51),[(31578,4),(31579,1)]⟩
 | 8842 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 52),[(31580,1)]⟩
 | 8843 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 53),[(31581,1)]⟩
 | 8844 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 54),[(31583,1)]⟩
 | 8845 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 55),[(31582,4),(31583,1)]⟩
 | 8846 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 56),[(31584,1)]⟩
 | 8847 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 57),[(31585,1)]⟩
 | 8848 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 58),[(31587,1)]⟩
 | 8849 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 59),[(31586,4),(31587,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B11.count
