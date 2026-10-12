import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5770 16
def localParent : Nat → Option Row
 | 5770 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 156),[(28508,1)]⟩
 | 5771 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 157),[(28509,1)]⟩
 | 5772 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 158),[(28511,1)]⟩
 | 5773 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 159),[(28510,4),(28511,1)]⟩
 | 5774 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 160),[(28512,1)]⟩
 | 5775 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 161),[(28513,1)]⟩
 | 5776 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 162),[(28515,1)]⟩
 | 5777 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 163),[(28514,4),(28515,1)]⟩
 | 5778 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 164),[(28516,1)]⟩
 | 5779 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 165),[(28517,1)]⟩
 | 5780 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 166),[(28519,1)]⟩
 | 5781 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 167),[(28518,4),(28519,1)]⟩
 | 5782 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 168),[(28520,1)]⟩
 | 5783 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 169),[(28521,1)]⟩
 | 5784 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 170),[(28523,1)]⟩
 | 5785 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 171),[(28522,4),(28523,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B05.count
