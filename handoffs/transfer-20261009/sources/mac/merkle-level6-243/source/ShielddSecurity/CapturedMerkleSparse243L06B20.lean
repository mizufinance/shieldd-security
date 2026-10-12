import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0028
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6010 16
def localParent : Nat → Option Row
 | 6010 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 74),[(28748,1)]⟩
 | 6011 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 75),[(28749,1)]⟩
 | 6012 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 76),[(28751,1)]⟩
 | 6013 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 77),[(28750,4),(28751,1)]⟩
 | 6014 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 78),[(28752,1)]⟩
 | 6015 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 79),[(28753,1)]⟩
 | 6016 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 80),[(28755,1)]⟩
 | 6017 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 81),[(28754,4),(28755,1)]⟩
 | 6018 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 82),[(28756,1)]⟩
 | 6019 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 83),[(28757,1)]⟩
 | 6020 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 84),[(28759,1)]⟩
 | 6021 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 85),[(28758,4),(28759,1)]⟩
 | 6022 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 86),[(28760,1)]⟩
 | 6023 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 87),[(28761,1)]⟩
 | 6024 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 88),[(28763,1)]⟩
 | 6025 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0028.inputs 89),[(28762,4),(28763,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B20.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B20.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B20.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B20.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B20.count
