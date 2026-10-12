import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CapturedArithmetic45B0017
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B09
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 92).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3714 16
def localParent : Nat → Option Row
 | 3714 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 268),[(26452,1)]⟩
 | 3715 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 269),[(26453,1)]⟩
 | 3716 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 270),[(26455,1)]⟩
 | 3717 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 271),[(26454,4),(26455,1)]⟩
 | 3718 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 272),[(26456,1)]⟩
 | 3719 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 273),[(26457,1)]⟩
 | 3720 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 274),[(26459,1)]⟩
 | 3721 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 275),[(26458,4),(26459,1)]⟩
 | 3722 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 276),[(26460,1)]⟩
 | 3723 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 277),[(26461,1)]⟩
 | 3724 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 0),[(26463,1)]⟩
 | 3725 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 1),[(26462,4),(26463,1)]⟩
 | 3726 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 2),[(26464,1)]⟩
 | 3727 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 3),[(26465,1)]⟩
 | 3728 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 4),[(26467,1)]⟩
 | 3729 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 5),[(26466,4),(26467,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B09.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B09.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B09.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B09.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B09.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B09.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B09.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B09.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B09.count
