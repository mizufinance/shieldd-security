import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B09
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 92).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5410 16
def localParent : Nat → Option Row
 | 5410 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 190),[(28148,1)]⟩
 | 5411 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 191),[(28149,1)]⟩
 | 5412 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 192),[(28151,1)]⟩
 | 5413 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 193),[(28150,4),(28151,1)]⟩
 | 5414 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 194),[(28152,1)]⟩
 | 5415 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 195),[(28153,1)]⟩
 | 5416 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 196),[(28155,1)]⟩
 | 5417 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 197),[(28154,4),(28155,1)]⟩
 | 5418 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 198),[(28156,1)]⟩
 | 5419 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 199),[(28157,1)]⟩
 | 5420 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 200),[(28159,1)]⟩
 | 5421 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 201),[(28158,4),(28159,1)]⟩
 | 5422 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 202),[(28160,1)]⟩
 | 5423 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 203),[(28161,1)]⟩
 | 5424 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 204),[(28163,1)]⟩
 | 5425 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 205),[(28162,4),(28163,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B09.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B09.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B09.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B09.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B09.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B09.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B09.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B09.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B09.count
