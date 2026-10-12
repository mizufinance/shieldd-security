import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3546 16
def localParent : Nat → Option Row
 | 3546 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 100),[(26284,1)]⟩
 | 3547 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 101),[(26285,1)]⟩
 | 3548 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 102),[(26287,1)]⟩
 | 3549 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 103),[(26286,4),(26287,1)]⟩
 | 3550 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 104),[(26288,1)]⟩
 | 3551 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 105),[(26289,1)]⟩
 | 3552 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 106),[(26291,1)]⟩
 | 3553 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 107),[(26290,4),(26291,1)]⟩
 | 3554 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 108),[(26292,1)]⟩
 | 3555 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 109),[(26293,1)]⟩
 | 3556 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 110),[(26295,1)]⟩
 | 3557 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 111),[(26294,4),(26295,1)]⟩
 | 3558 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 112),[(26296,1)]⟩
 | 3559 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 113),[(26297,1)]⟩
 | 3560 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 114),[(26299,1)]⟩
 | 3561 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 115),[(26298,4),(26299,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B25.count
