import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0019
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4186 16
def localParent : Nat → Option Row
 | 4186 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 64),[(26924,1)]⟩
 | 4187 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 65),[(26925,1)]⟩
 | 4188 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 66),[(26927,1)]⟩
 | 4189 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 67),[(26926,4),(26927,1)]⟩
 | 4190 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 68),[(26928,1)]⟩
 | 4191 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 69),[(26929,1)]⟩
 | 4192 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 70),[(26931,1)]⟩
 | 4193 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 71),[(26930,4),(26931,1)]⟩
 | 4194 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 72),[(26932,1)]⟩
 | 4195 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 73),[(26933,1)]⟩
 | 4196 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 74),[(26935,1)]⟩
 | 4197 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 75),[(26934,4),(26935,1)]⟩
 | 4198 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 76),[(26936,1)]⟩
 | 4199 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 77),[(26937,1)]⟩
 | 4200 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 78),[(26939,1)]⟩
 | 4201 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 79),[(26938,4),(26939,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B12.count
