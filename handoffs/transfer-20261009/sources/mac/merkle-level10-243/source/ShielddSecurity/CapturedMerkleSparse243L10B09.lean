import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B09
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 92).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7530 16
def localParent : Nat → Option Row
 | 7530 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 250),[(30268,1)]⟩
 | 7531 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 251),[(30269,1)]⟩
 | 7532 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 252),[(30271,1)]⟩
 | 7533 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 253),[(30270,4),(30271,1)]⟩
 | 7534 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 254),[(30272,1)]⟩
 | 7535 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 255),[(30273,1)]⟩
 | 7536 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 256),[(30275,1)]⟩
 | 7537 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 257),[(30274,4),(30275,1)]⟩
 | 7538 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 258),[(30276,1)]⟩
 | 7539 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 259),[(30277,1)]⟩
 | 7540 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 260),[(30279,1)]⟩
 | 7541 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 261),[(30278,4),(30279,1)]⟩
 | 7542 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 262),[(30280,1)]⟩
 | 7543 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 263),[(30281,1)]⟩
 | 7544 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 264),[(30283,1)]⟩
 | 7545 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 265),[(30282,4),(30283,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B09.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B09.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B09.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B09.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B09.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B09.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B09.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B09.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B09.count
