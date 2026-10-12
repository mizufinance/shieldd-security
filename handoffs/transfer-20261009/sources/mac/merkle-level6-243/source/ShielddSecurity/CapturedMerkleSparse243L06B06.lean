import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5786 16
def localParent : Nat → Option Row
 | 5786 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 172),[(28524,1)]⟩
 | 5787 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 173),[(28525,1)]⟩
 | 5788 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 174),[(28527,1)]⟩
 | 5789 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 175),[(28526,4),(28527,1)]⟩
 | 5790 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 176),[(28528,1)]⟩
 | 5791 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 177),[(28529,1)]⟩
 | 5792 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 178),[(28531,1)]⟩
 | 5793 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 179),[(28530,4),(28531,1)]⟩
 | 5794 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 180),[(28532,1)]⟩
 | 5795 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 181),[(28533,1)]⟩
 | 5796 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 182),[(28535,1)]⟩
 | 5797 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 183),[(28534,4),(28535,1)]⟩
 | 5798 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 184),[(28536,1)]⟩
 | 5799 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 185),[(28537,1)]⟩
 | 5800 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 186),[(28539,1)]⟩
 | 5801 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 187),[(28538,4),(28539,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B06.count
