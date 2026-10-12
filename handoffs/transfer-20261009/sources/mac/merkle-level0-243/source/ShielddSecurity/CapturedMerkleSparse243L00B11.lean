import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0015
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3322 16
def localParent : Nat → Option Row
 | 3322 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 2),[(26060,1)]⟩
 | 3323 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 3),[(26061,1)]⟩
 | 3324 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 4),[(26063,1)]⟩
 | 3325 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 5),[(26062,4),(26063,1)]⟩
 | 3326 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 6),[(26064,1)]⟩
 | 3327 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 7),[(26065,1)]⟩
 | 3328 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 8),[(26067,1)]⟩
 | 3329 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 9),[(26066,4),(26067,1)]⟩
 | 3330 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 10),[(26068,1)]⟩
 | 3331 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 11),[(26069,1)]⟩
 | 3332 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 12),[(26071,1)]⟩
 | 3333 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 13),[(26070,4),(26071,1)]⟩
 | 3334 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 14),[(26072,1)]⟩
 | 3335 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 15),[(26073,1)]⟩
 | 3336 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 16),[(26075,1)]⟩
 | 3337 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 17),[(26074,4),(26075,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B11.count
