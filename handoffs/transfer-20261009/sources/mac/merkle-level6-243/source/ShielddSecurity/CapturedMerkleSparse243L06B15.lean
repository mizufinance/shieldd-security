import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CapturedArithmetic45B0028
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5930 16
def localParent : Nat → Option Row
 | 5930 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 316),[(28668,1)]⟩
 | 5931 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 317),[(28669,1)]⟩
 | 5932 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 318),[(28671,1)]⟩
 | 5933 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 319),[(28670,4),(28671,1)]⟩
 | 5934 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 320),[(28672,1)]⟩
 | 5935 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 321),[(28673,1)]⟩
 | 5936 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 0),[(28675,1)]⟩
 | 5937 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 1),[(28674,4),(28675,1)]⟩
 | 5938 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 2),[(28676,1)]⟩
 | 5939 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 3),[(28677,1)]⟩
 | 5940 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 4),[(28679,1)]⟩
 | 5941 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 5),[(28678,4),(28679,1)]⟩
 | 5942 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 6),[(28680,1)]⟩
 | 5943 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 7),[(28681,1)]⟩
 | 5944 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 8),[(28683,1)]⟩
 | 5945 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 9),[(28682,4),(28683,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B15.count
