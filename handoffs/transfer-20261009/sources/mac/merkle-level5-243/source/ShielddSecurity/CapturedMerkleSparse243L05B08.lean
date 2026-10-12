import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B08
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 76).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5394 16
def localParent : Nat → Option Row
 | 5394 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 174),[(28132,1)]⟩
 | 5395 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 175),[(28133,1)]⟩
 | 5396 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 176),[(28135,1)]⟩
 | 5397 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 177),[(28134,4),(28135,1)]⟩
 | 5398 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 178),[(28136,1)]⟩
 | 5399 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 179),[(28137,1)]⟩
 | 5400 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 180),[(28139,1)]⟩
 | 5401 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 181),[(28138,4),(28139,1)]⟩
 | 5402 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 182),[(28140,1)]⟩
 | 5403 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 183),[(28141,1)]⟩
 | 5404 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 184),[(28143,1)]⟩
 | 5405 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 185),[(28142,4),(28143,1)]⟩
 | 5406 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 186),[(28144,1)]⟩
 | 5407 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 187),[(28145,1)]⟩
 | 5408 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 188),[(28147,1)]⟩
 | 5409 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 189),[(28146,4),(28147,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B08

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B08.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B08.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B08.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B08.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B08.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B08.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B08.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B08.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B08.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B08.count
