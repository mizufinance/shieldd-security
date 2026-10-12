import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0042
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8818 16
def localParent : Nat → Option Row
 | 8818 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 28),[(31556,1)]⟩
 | 8819 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 29),[(31557,1)]⟩
 | 8820 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 30),[(31559,1)]⟩
 | 8821 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 31),[(31558,4),(31559,1)]⟩
 | 8822 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 32),[(31560,1)]⟩
 | 8823 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 33),[(31561,1)]⟩
 | 8824 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 34),[(31563,1)]⟩
 | 8825 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 35),[(31562,4),(31563,1)]⟩
 | 8826 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 36),[(31564,1)]⟩
 | 8827 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 37),[(31565,1)]⟩
 | 8828 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 38),[(31567,1)]⟩
 | 8829 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 39),[(31566,4),(31567,1)]⟩
 | 8830 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 40),[(31568,1)]⟩
 | 8831 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 41),[(31569,1)]⟩
 | 8832 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 42),[(31571,1)]⟩
 | 8833 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 43),[(31570,4),(31571,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B10.count
