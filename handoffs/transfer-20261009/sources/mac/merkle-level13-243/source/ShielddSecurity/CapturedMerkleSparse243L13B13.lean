import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0042
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8866 16
def localParent : Nat → Option Row
 | 8866 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 76),[(31604,1)]⟩
 | 8867 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 77),[(31605,1)]⟩
 | 8868 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 78),[(31607,1)]⟩
 | 8869 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 79),[(31606,4),(31607,1)]⟩
 | 8870 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 80),[(31608,1)]⟩
 | 8871 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 81),[(31609,1)]⟩
 | 8872 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 82),[(31611,1)]⟩
 | 8873 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 83),[(31610,4),(31611,1)]⟩
 | 8874 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 84),[(31612,1)]⟩
 | 8875 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 85),[(31613,1)]⟩
 | 8876 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 86),[(31615,1)]⟩
 | 8877 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 87),[(31614,4),(31615,1)]⟩
 | 8878 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 88),[(31616,1)]⟩
 | 8879 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 89),[(31617,1)]⟩
 | 8880 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 90),[(31619,1)]⟩
 | 8881 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 91),[(31618,4),(31619,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B13.count
