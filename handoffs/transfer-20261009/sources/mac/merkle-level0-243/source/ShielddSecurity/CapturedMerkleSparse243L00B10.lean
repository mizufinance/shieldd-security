import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0014
import ShielddSecurity.CapturedArithmetic45B0015
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3306 16
def localParent : Nat → Option Row
 | 3306 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 276),[(26044,1)]⟩
 | 3307 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 277),[(26045,1)]⟩
 | 3308 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 278),[(26047,1)]⟩
 | 3309 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 279),[(26046,4),(26047,1)]⟩
 | 3310 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 280),[(26048,1)]⟩
 | 3311 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 281),[(26049,1)]⟩
 | 3312 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 282),[(26051,1)]⟩
 | 3313 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 283),[(26050,4),(26051,1)]⟩
 | 3314 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 284),[(26052,1)]⟩
 | 3315 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 285),[(26053,1)]⟩
 | 3316 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 286),[(26055,1)]⟩
 | 3317 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 287),[(26054,4),(26055,1)]⟩
 | 3318 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 288),[(26056,1)]⟩
 | 3319 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 289),[(26057,1)]⟩
 | 3320 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 0),[(26059,1)]⟩
 | 3321 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 1),[(26058,4),(26059,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B10.count
