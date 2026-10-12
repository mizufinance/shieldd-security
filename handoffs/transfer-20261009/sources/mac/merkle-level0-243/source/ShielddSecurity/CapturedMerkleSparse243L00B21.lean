import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3482 16
def localParent : Nat → Option Row
 | 3482 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 36),[(26220,1)]⟩
 | 3483 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 37),[(26221,1)]⟩
 | 3484 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 38),[(26223,1)]⟩
 | 3485 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 39),[(26222,4),(26223,1)]⟩
 | 3486 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 40),[(26224,1)]⟩
 | 3487 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 41),[(26225,1)]⟩
 | 3488 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 42),[(26227,1)]⟩
 | 3489 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 43),[(26226,4),(26227,1)]⟩
 | 3490 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 44),[(26228,1)]⟩
 | 3491 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 45),[(26229,1)]⟩
 | 3492 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 46),[(26231,1)]⟩
 | 3493 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 47),[(26230,4),(26231,1)]⟩
 | 3494 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 48),[(26232,1)]⟩
 | 3495 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 49),[(26233,1)]⟩
 | 3496 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 50),[(26235,1)]⟩
 | 3497 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 51),[(26234,4),(26235,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B21.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B21.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B21.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B21.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B21.count
