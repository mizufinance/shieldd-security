import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B09
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 92).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5834 16
def localParent : Nat → Option Row
 | 5834 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 220),[(28572,1)]⟩
 | 5835 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 221),[(28573,1)]⟩
 | 5836 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 222),[(28575,1)]⟩
 | 5837 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 223),[(28574,4),(28575,1)]⟩
 | 5838 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 224),[(28576,1)]⟩
 | 5839 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 225),[(28577,1)]⟩
 | 5840 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 226),[(28579,1)]⟩
 | 5841 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 227),[(28578,4),(28579,1)]⟩
 | 5842 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 228),[(28580,1)]⟩
 | 5843 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 229),[(28581,1)]⟩
 | 5844 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 230),[(28583,1)]⟩
 | 5845 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 231),[(28582,4),(28583,1)]⟩
 | 5846 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 232),[(28584,1)]⟩
 | 5847 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 233),[(28585,1)]⟩
 | 5848 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 234),[(28587,1)]⟩
 | 5849 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 235),[(28586,4),(28587,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B09.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B09.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B09.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B09.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B09.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B09.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B09.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B09.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B09.count
