import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7346 16
def localParent : Nat → Option Row
 | 7346 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 66),[(30084,1)]⟩
 | 7347 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 67),[(30085,1)]⟩
 | 7348 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 68),[(30087,1)]⟩
 | 7349 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 69),[(30086,4),(30087,1)]⟩
 | 7350 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 70),[(30088,1)]⟩
 | 7351 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 71),[(30089,1)]⟩
 | 7352 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 72),[(30091,1)]⟩
 | 7353 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 73),[(30090,4),(30091,1)]⟩
 | 7354 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 74),[(30092,1)]⟩
 | 7355 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 75),[(30093,1)]⟩
 | 7356 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 76),[(30095,1)]⟩
 | 7357 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 77),[(30094,4),(30095,1)]⟩
 | 7358 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 78),[(30096,1)]⟩
 | 7359 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 79),[(30097,1)]⟩
 | 7360 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 80),[(30099,1)]⟩
 | 7361 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 81),[(30098,4),(30099,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B24.count
