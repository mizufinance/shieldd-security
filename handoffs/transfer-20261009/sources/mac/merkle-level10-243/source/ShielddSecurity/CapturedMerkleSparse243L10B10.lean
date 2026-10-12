import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7546 16
def localParent : Nat → Option Row
 | 7546 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 266),[(30284,1)]⟩
 | 7547 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 267),[(30285,1)]⟩
 | 7548 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 268),[(30287,1)]⟩
 | 7549 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 269),[(30286,4),(30287,1)]⟩
 | 7550 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 270),[(30288,1)]⟩
 | 7551 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 271),[(30289,1)]⟩
 | 7552 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 272),[(30291,1)]⟩
 | 7553 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 273),[(30290,4),(30291,1)]⟩
 | 7554 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 274),[(30292,1)]⟩
 | 7555 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 275),[(30293,1)]⟩
 | 7556 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 276),[(30295,1)]⟩
 | 7557 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 277),[(30294,4),(30295,1)]⟩
 | 7558 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 278),[(30296,1)]⟩
 | 7559 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 279),[(30297,1)]⟩
 | 7560 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 280),[(30299,1)]⟩
 | 7561 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 281),[(30298,4),(30299,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B10.count
