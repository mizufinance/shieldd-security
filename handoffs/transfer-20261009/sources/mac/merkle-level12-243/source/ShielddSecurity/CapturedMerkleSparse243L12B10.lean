import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0040
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8394 16
def localParent : Nat → Option Row
 | 8394 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 3),[(31132,1)]⟩
 | 8395 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 4),[(31133,1)]⟩
 | 8396 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 5),[(31135,1)]⟩
 | 8397 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 6),[(31134,4),(31135,1)]⟩
 | 8398 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 7),[(31136,1)]⟩
 | 8399 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 8),[(31137,1)]⟩
 | 8400 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 9),[(31139,1)]⟩
 | 8401 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 10),[(31138,4),(31139,1)]⟩
 | 8402 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 11),[(31140,1)]⟩
 | 8403 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 12),[(31141,1)]⟩
 | 8404 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 13),[(31143,1)]⟩
 | 8405 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 14),[(31142,4),(31143,1)]⟩
 | 8406 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 15),[(31144,1)]⟩
 | 8407 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 16),[(31145,1)]⟩
 | 8408 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 17),[(31147,1)]⟩
 | 8409 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 18),[(31146,4),(31147,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B10.count
