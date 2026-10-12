import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0026
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5538 16
def localParent : Nat → Option Row
 | 5538 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 16),[(28276,1)]⟩
 | 5539 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 17),[(28277,1)]⟩
 | 5540 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 18),[(28279,1)]⟩
 | 5541 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 19),[(28278,4),(28279,1)]⟩
 | 5542 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 20),[(28280,1)]⟩
 | 5543 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 21),[(28281,1)]⟩
 | 5544 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 22),[(28283,1)]⟩
 | 5545 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 23),[(28282,4),(28283,1)]⟩
 | 5546 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 24),[(28284,1)]⟩
 | 5547 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 25),[(28285,1)]⟩
 | 5548 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 26),[(28287,1)]⟩
 | 5549 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 27),[(28286,4),(28287,1)]⟩
 | 5550 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 28),[(28288,1)]⟩
 | 5551 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 29),[(28289,1)]⟩
 | 5552 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 30),[(28291,1)]⟩
 | 5553 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 31),[(28290,4),(28291,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B17.count
