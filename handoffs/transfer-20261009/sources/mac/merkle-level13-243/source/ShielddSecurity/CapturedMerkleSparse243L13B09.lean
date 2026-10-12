import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0042
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B09
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 92).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8802 16
def localParent : Nat → Option Row
 | 8802 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 12),[(31540,1)]⟩
 | 8803 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 13),[(31541,1)]⟩
 | 8804 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 14),[(31543,1)]⟩
 | 8805 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 15),[(31542,4),(31543,1)]⟩
 | 8806 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 16),[(31544,1)]⟩
 | 8807 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 17),[(31545,1)]⟩
 | 8808 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 18),[(31547,1)]⟩
 | 8809 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 19),[(31546,4),(31547,1)]⟩
 | 8810 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 20),[(31548,1)]⟩
 | 8811 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 21),[(31549,1)]⟩
 | 8812 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 22),[(31551,1)]⟩
 | 8813 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 23),[(31550,4),(31551,1)]⟩
 | 8814 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 24),[(31552,1)]⟩
 | 8815 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 25),[(31553,1)]⟩
 | 8816 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 26),[(31555,1)]⟩
 | 8817 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 27),[(31554,4),(31555,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B09.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B09.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B09.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B09.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B09.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B09.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B09.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B09.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B09.count
