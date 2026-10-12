import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0015
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3434 16
def localParent : Nat → Option Row
 | 3434 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 114),[(26172,1)]⟩
 | 3435 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 115),[(26173,1)]⟩
 | 3436 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 116),[(26175,1)]⟩
 | 3437 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 117),[(26174,4),(26175,1)]⟩
 | 3438 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 118),[(26176,1)]⟩
 | 3439 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 119),[(26177,1)]⟩
 | 3440 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 120),[(26179,1)]⟩
 | 3441 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 121),[(26178,4),(26179,1)]⟩
 | 3442 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 122),[(26180,1)]⟩
 | 3443 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 123),[(26181,1)]⟩
 | 3444 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 124),[(26183,1)]⟩
 | 3445 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 125),[(26182,4),(26183,1)]⟩
 | 3446 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 0),[(26184,1)]⟩
 | 3447 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 1),[(26185,1)]⟩
 | 3448 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 2),[(26187,1)]⟩
 | 3449 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 3),[(26186,4),(26187,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B18.count
