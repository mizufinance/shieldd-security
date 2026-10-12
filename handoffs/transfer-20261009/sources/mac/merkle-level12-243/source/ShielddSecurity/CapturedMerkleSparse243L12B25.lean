import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0041
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8634 16
def localParent : Nat → Option Row
 | 8634 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 106),[(31372,1)]⟩
 | 8635 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 107),[(31373,1)]⟩
 | 8636 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 108),[(31375,1)]⟩
 | 8637 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 109),[(31374,4),(31375,1)]⟩
 | 8638 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 110),[(31376,1)]⟩
 | 8639 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 111),[(31377,1)]⟩
 | 8640 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 112),[(31379,1)]⟩
 | 8641 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 113),[(31378,4),(31379,1)]⟩
 | 8642 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 114),[(31380,1)]⟩
 | 8643 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 115),[(31381,1)]⟩
 | 8644 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 116),[(31383,1)]⟩
 | 8645 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 117),[(31382,4),(31383,1)]⟩
 | 8646 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 118),[(31384,1)]⟩
 | 8647 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 119),[(31385,1)]⟩
 | 8648 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 120),[(31387,1)]⟩
 | 8649 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 121),[(31386,4),(31387,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B25.count
