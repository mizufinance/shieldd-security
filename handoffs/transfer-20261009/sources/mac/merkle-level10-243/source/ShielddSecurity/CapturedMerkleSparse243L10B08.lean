import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B08
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 76).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7514 16
def localParent : Nat → Option Row
 | 7514 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 234),[(30252,1)]⟩
 | 7515 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 235),[(30253,1)]⟩
 | 7516 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 236),[(30255,1)]⟩
 | 7517 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 237),[(30254,4),(30255,1)]⟩
 | 7518 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 238),[(30256,1)]⟩
 | 7519 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 239),[(30257,1)]⟩
 | 7520 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 240),[(30259,1)]⟩
 | 7521 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 241),[(30258,4),(30259,1)]⟩
 | 7522 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 242),[(30260,1)]⟩
 | 7523 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 243),[(30261,1)]⟩
 | 7524 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 244),[(30263,1)]⟩
 | 7525 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 245),[(30262,4),(30263,1)]⟩
 | 7526 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 246),[(30264,1)]⟩
 | 7527 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 247),[(30265,1)]⟩
 | 7528 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 248),[(30267,1)]⟩
 | 7529 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 249),[(30266,4),(30267,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B08

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B08.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B08.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B08.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B08.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B08.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B08.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B08.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B08.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B08.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B08.count
