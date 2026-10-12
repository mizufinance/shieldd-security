import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5378 16
def localParent : Nat → Option Row
 | 5378 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 158),[(28116,1)]⟩
 | 5379 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 159),[(28117,1)]⟩
 | 5380 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 160),[(28119,1)]⟩
 | 5381 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 161),[(28118,4),(28119,1)]⟩
 | 5382 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 162),[(28120,1)]⟩
 | 5383 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 163),[(28121,1)]⟩
 | 5384 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 164),[(28123,1)]⟩
 | 5385 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 165),[(28122,4),(28123,1)]⟩
 | 5386 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 166),[(28124,1)]⟩
 | 5387 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 167),[(28125,1)]⟩
 | 5388 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 168),[(28127,1)]⟩
 | 5389 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 169),[(28126,4),(28127,1)]⟩
 | 5390 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 170),[(28128,1)]⟩
 | 5391 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 171),[(28129,1)]⟩
 | 5392 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 172),[(28131,1)]⟩
 | 5393 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 173),[(28130,4),(28131,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B07.count
