import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6714 16
def localParent : Nat → Option Row
 | 6714 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 266),[(29452,1)]⟩
 | 6715 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 267),[(29453,1)]⟩
 | 6716 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 268),[(29455,1)]⟩
 | 6717 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 269),[(29454,4),(29455,1)]⟩
 | 6718 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 270),[(29456,1)]⟩
 | 6719 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 271),[(29457,1)]⟩
 | 6720 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 272),[(29459,1)]⟩
 | 6721 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 273),[(29458,4),(29459,1)]⟩
 | 6722 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 274),[(29460,1)]⟩
 | 6723 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 275),[(29461,1)]⟩
 | 6724 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 276),[(29463,1)]⟩
 | 6725 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 277),[(29462,4),(29463,1)]⟩
 | 6726 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 278),[(29464,1)]⟩
 | 6727 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 279),[(29465,1)]⟩
 | 6728 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 280),[(29467,1)]⟩
 | 6729 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 281),[(29466,4),(29467,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B11.count
