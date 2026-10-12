import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B14
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 172).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5914 16
def localParent : Nat → Option Row
 | 5914 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 300),[(28652,1)]⟩
 | 5915 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 301),[(28653,1)]⟩
 | 5916 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 302),[(28655,1)]⟩
 | 5917 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 303),[(28654,4),(28655,1)]⟩
 | 5918 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 304),[(28656,1)]⟩
 | 5919 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 305),[(28657,1)]⟩
 | 5920 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 306),[(28659,1)]⟩
 | 5921 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 307),[(28658,4),(28659,1)]⟩
 | 5922 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 308),[(28660,1)]⟩
 | 5923 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 309),[(28661,1)]⟩
 | 5924 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 310),[(28663,1)]⟩
 | 5925 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 311),[(28662,4),(28663,1)]⟩
 | 5926 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 312),[(28664,1)]⟩
 | 5927 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 313),[(28665,1)]⟩
 | 5928 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 314),[(28667,1)]⟩
 | 5929 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 315),[(28666,4),(28667,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B14

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B14.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B14.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B14.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B14.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B14.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B14.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B14.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B14.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B14.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B14.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B14.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B14.count
