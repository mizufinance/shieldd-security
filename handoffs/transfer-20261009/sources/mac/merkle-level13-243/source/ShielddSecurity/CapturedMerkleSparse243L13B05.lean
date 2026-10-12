import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0041
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8738 16
def localParent : Nat → Option Row
 | 8738 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 210),[(31476,1)]⟩
 | 8739 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 211),[(31477,1)]⟩
 | 8740 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 212),[(31479,1)]⟩
 | 8741 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 213),[(31478,4),(31479,1)]⟩
 | 8742 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 214),[(31480,1)]⟩
 | 8743 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 215),[(31481,1)]⟩
 | 8744 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 216),[(31483,1)]⟩
 | 8745 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 217),[(31482,4),(31483,1)]⟩
 | 8746 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 218),[(31484,1)]⟩
 | 8747 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 219),[(31485,1)]⟩
 | 8748 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 220),[(31487,1)]⟩
 | 8749 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 221),[(31486,4),(31487,1)]⟩
 | 8750 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 222),[(31488,1)]⟩
 | 8751 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 223),[(31489,1)]⟩
 | 8752 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 224),[(31491,1)]⟩
 | 8753 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 225),[(31490,4),(31491,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B05.count
