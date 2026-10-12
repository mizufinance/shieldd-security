import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L11B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5512)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7922 16
def localParent : Nat → Option Row
 | 7922 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 226),[(30660,1)]⟩
 | 7923 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 227),[(30661,1)]⟩
 | 7924 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 228),[(30663,1)]⟩
 | 7925 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 229),[(30662,4),(30663,1)]⟩
 | 7926 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 230),[(30664,1)]⟩
 | 7927 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 231),[(30665,1)]⟩
 | 7928 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 232),[(30667,1)]⟩
 | 7929 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 233),[(30666,4),(30667,1)]⟩
 | 7930 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 234),[(30668,1)]⟩
 | 7931 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 235),[(30669,1)]⟩
 | 7932 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 236),[(30671,1)]⟩
 | 7933 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 237),[(30670,4),(30671,1)]⟩
 | 7934 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 238),[(30672,1)]⟩
 | 7935 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 239),[(30673,1)]⟩
 | 7936 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 240),[(30675,1)]⟩
 | 7937 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 241),[(30674,4),(30675,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L11B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L11B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L11B07.count
