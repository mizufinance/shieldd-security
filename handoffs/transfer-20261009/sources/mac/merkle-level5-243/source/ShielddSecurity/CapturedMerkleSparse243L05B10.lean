import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5426 16
def localParent : Nat → Option Row
 | 5426 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 206),[(28164,1)]⟩
 | 5427 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 207),[(28165,1)]⟩
 | 5428 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 208),[(28167,1)]⟩
 | 5429 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 209),[(28166,4),(28167,1)]⟩
 | 5430 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 210),[(28168,1)]⟩
 | 5431 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 211),[(28169,1)]⟩
 | 5432 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 212),[(28171,1)]⟩
 | 5433 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 213),[(28170,4),(28171,1)]⟩
 | 5434 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 214),[(28172,1)]⟩
 | 5435 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 215),[(28173,1)]⟩
 | 5436 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 216),[(28175,1)]⟩
 | 5437 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 217),[(28174,4),(28175,1)]⟩
 | 5438 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 218),[(28176,1)]⟩
 | 5439 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 219),[(28177,1)]⟩
 | 5440 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 220),[(28179,1)]⟩
 | 5441 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 221),[(28178,4),(28179,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B10.count
