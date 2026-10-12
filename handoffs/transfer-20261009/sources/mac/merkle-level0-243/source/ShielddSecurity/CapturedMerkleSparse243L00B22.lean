import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 300).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3498 16
def localParent : Nat → Option Row
 | 3498 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 52),[(26236,1)]⟩
 | 3499 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 53),[(26237,1)]⟩
 | 3500 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 54),[(26239,1)]⟩
 | 3501 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 55),[(26238,4),(26239,1)]⟩
 | 3502 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 56),[(26240,1)]⟩
 | 3503 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 57),[(26241,1)]⟩
 | 3504 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 58),[(26243,1)]⟩
 | 3505 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 59),[(26242,4),(26243,1)]⟩
 | 3506 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 60),[(26244,1)]⟩
 | 3507 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 61),[(26245,1)]⟩
 | 3508 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 62),[(26247,1)]⟩
 | 3509 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 63),[(26246,4),(26247,1)]⟩
 | 3510 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 64),[(26248,1)]⟩
 | 3511 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 65),[(26249,1)]⟩
 | 3512 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 66),[(26251,1)]⟩
 | 3513 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 67),[(26250,4),(26251,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B22.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B22.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B22.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B22.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B22.count
