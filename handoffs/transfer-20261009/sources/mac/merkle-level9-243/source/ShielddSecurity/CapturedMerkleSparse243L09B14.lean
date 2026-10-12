import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0034
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B14
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 172).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7186 16
def localParent : Nat → Option Row
 | 7186 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 16),[(29924,1)]⟩
 | 7187 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 17),[(29925,1)]⟩
 | 7188 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 18),[(29927,1)]⟩
 | 7189 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 19),[(29926,4),(29927,1)]⟩
 | 7190 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 20),[(29928,1)]⟩
 | 7191 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 21),[(29929,1)]⟩
 | 7192 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 22),[(29931,1)]⟩
 | 7193 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 23),[(29930,4),(29931,1)]⟩
 | 7194 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 24),[(29932,1)]⟩
 | 7195 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 25),[(29933,1)]⟩
 | 7196 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 26),[(29935,1)]⟩
 | 7197 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 27),[(29934,4),(29935,1)]⟩
 | 7198 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 28),[(29936,1)]⟩
 | 7199 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 29),[(29937,1)]⟩
 | 7200 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 30),[(29939,1)]⟩
 | 7201 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 31),[(29938,4),(29939,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B14

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B14.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B14.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B14.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B14.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B14.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B14.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B14.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B14.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B14.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B14.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B14.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B14.count
