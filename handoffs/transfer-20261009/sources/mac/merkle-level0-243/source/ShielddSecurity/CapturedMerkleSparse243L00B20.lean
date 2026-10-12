import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3466 16
def localParent : Nat → Option Row
 | 3466 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 20),[(26204,1)]⟩
 | 3467 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 21),[(26205,1)]⟩
 | 3468 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 22),[(26207,1)]⟩
 | 3469 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 23),[(26206,4),(26207,1)]⟩
 | 3470 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 24),[(26208,1)]⟩
 | 3471 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 25),[(26209,1)]⟩
 | 3472 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 26),[(26211,1)]⟩
 | 3473 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 27),[(26210,4),(26211,1)]⟩
 | 3474 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 28),[(26212,1)]⟩
 | 3475 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 29),[(26213,1)]⟩
 | 3476 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 30),[(26215,1)]⟩
 | 3477 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 31),[(26214,4),(26215,1)]⟩
 | 3478 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 32),[(26216,1)]⟩
 | 3479 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 33),[(26217,1)]⟩
 | 3480 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 34),[(26219,1)]⟩
 | 3481 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 35),[(26218,4),(26219,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B20.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B20.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B20.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B20.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B20.count
