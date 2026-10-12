import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0042
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8898 16
def localParent : Nat → Option Row
 | 8898 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 108),[(31636,1)]⟩
 | 8899 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 109),[(31637,1)]⟩
 | 8900 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 110),[(31639,1)]⟩
 | 8901 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 111),[(31638,4),(31639,1)]⟩
 | 8902 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 112),[(31640,1)]⟩
 | 8903 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 113),[(31641,1)]⟩
 | 8904 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 114),[(31643,1)]⟩
 | 8905 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 115),[(31642,4),(31643,1)]⟩
 | 8906 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 116),[(31644,1)]⟩
 | 8907 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 117),[(31645,1)]⟩
 | 8908 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 118),[(31647,1)]⟩
 | 8909 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 119),[(31646,4),(31647,1)]⟩
 | 8910 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 120),[(31648,1)]⟩
 | 8911 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 121),[(31649,1)]⟩
 | 8912 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 122),[(31651,1)]⟩
 | 8913 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 123),[(31650,4),(31651,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B15.count
