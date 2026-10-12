import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0015
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B14
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 172).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3370 16
def localParent : Nat → Option Row
 | 3370 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 50),[(26108,1)]⟩
 | 3371 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 51),[(26109,1)]⟩
 | 3372 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 52),[(26111,1)]⟩
 | 3373 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 53),[(26110,4),(26111,1)]⟩
 | 3374 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 54),[(26112,1)]⟩
 | 3375 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 55),[(26113,1)]⟩
 | 3376 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 56),[(26115,1)]⟩
 | 3377 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 57),[(26114,4),(26115,1)]⟩
 | 3378 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 58),[(26116,1)]⟩
 | 3379 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 59),[(26117,1)]⟩
 | 3380 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 60),[(26119,1)]⟩
 | 3381 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 61),[(26118,4),(26119,1)]⟩
 | 3382 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 62),[(26120,1)]⟩
 | 3383 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 63),[(26121,1)]⟩
 | 3384 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 64),[(26123,1)]⟩
 | 3385 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 65),[(26122,4),(26123,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B14

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B14.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B14.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B14.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B14.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B14.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B14.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B14.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B14.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B14.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B14.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B14.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B14.count
