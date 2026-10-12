import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0015
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3354 16
def localParent : Nat → Option Row
 | 3354 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 34),[(26092,1)]⟩
 | 3355 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 35),[(26093,1)]⟩
 | 3356 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 36),[(26095,1)]⟩
 | 3357 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 37),[(26094,4),(26095,1)]⟩
 | 3358 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 38),[(26096,1)]⟩
 | 3359 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 39),[(26097,1)]⟩
 | 3360 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 40),[(26099,1)]⟩
 | 3361 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 41),[(26098,4),(26099,1)]⟩
 | 3362 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 42),[(26100,1)]⟩
 | 3363 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 43),[(26101,1)]⟩
 | 3364 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 44),[(26103,1)]⟩
 | 3365 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 45),[(26102,4),(26103,1)]⟩
 | 3366 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 46),[(26104,1)]⟩
 | 3367 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 47),[(26105,1)]⟩
 | 3368 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 48),[(26107,1)]⟩
 | 3369 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 49),[(26106,4),(26107,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B13.count
