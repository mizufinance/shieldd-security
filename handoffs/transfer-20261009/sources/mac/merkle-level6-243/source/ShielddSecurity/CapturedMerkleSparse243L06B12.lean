import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5882 16
def localParent : Nat → Option Row
 | 5882 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 268),[(28620,1)]⟩
 | 5883 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 269),[(28621,1)]⟩
 | 5884 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 270),[(28623,1)]⟩
 | 5885 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 271),[(28622,4),(28623,1)]⟩
 | 5886 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 272),[(28624,1)]⟩
 | 5887 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 273),[(28625,1)]⟩
 | 5888 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 274),[(28627,1)]⟩
 | 5889 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 275),[(28626,4),(28627,1)]⟩
 | 5890 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 276),[(28628,1)]⟩
 | 5891 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 277),[(28629,1)]⟩
 | 5892 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 278),[(28631,1)]⟩
 | 5893 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 279),[(28630,4),(28631,1)]⟩
 | 5894 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 280),[(28632,1)]⟩
 | 5895 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 281),[(28633,1)]⟩
 | 5896 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 282),[(28635,1)]⟩
 | 5897 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 283),[(28634,4),(28635,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B12.count
