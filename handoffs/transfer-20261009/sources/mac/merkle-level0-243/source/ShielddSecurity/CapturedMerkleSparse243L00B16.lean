import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0015
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3402 16
def localParent : Nat → Option Row
 | 3402 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 82),[(26140,1)]⟩
 | 3403 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 83),[(26141,1)]⟩
 | 3404 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 84),[(26143,1)]⟩
 | 3405 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 85),[(26142,4),(26143,1)]⟩
 | 3406 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 86),[(26144,1)]⟩
 | 3407 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 87),[(26145,1)]⟩
 | 3408 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 88),[(26147,1)]⟩
 | 3409 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 89),[(26146,4),(26147,1)]⟩
 | 3410 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 90),[(26148,1)]⟩
 | 3411 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 91),[(26149,1)]⟩
 | 3412 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 92),[(26151,1)]⟩
 | 3413 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 93),[(26150,4),(26151,1)]⟩
 | 3414 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 94),[(26152,1)]⟩
 | 3415 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 95),[(26153,1)]⟩
 | 3416 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 96),[(26155,1)]⟩
 | 3417 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 97),[(26154,4),(26155,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B16.count
