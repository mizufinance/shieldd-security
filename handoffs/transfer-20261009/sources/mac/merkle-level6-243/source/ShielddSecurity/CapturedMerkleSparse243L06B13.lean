import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5898 16
def localParent : Nat → Option Row
 | 5898 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 284),[(28636,1)]⟩
 | 5899 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 285),[(28637,1)]⟩
 | 5900 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 286),[(28639,1)]⟩
 | 5901 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 287),[(28638,4),(28639,1)]⟩
 | 5902 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 288),[(28640,1)]⟩
 | 5903 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 289),[(28641,1)]⟩
 | 5904 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 290),[(28643,1)]⟩
 | 5905 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 291),[(28642,4),(28643,1)]⟩
 | 5906 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 292),[(28644,1)]⟩
 | 5907 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 293),[(28645,1)]⟩
 | 5908 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 294),[(28647,1)]⟩
 | 5909 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 295),[(28646,4),(28647,1)]⟩
 | 5910 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 296),[(28648,1)]⟩
 | 5911 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 297),[(28649,1)]⟩
 | 5912 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 298),[(28651,1)]⟩
 | 5913 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 299),[(28650,4),(28651,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B13.count
