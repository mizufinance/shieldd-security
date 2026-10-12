import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0019
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4202 16
def localParent : Nat → Option Row
 | 4202 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 80),[(26940,1)]⟩
 | 4203 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 81),[(26941,1)]⟩
 | 4204 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 82),[(26943,1)]⟩
 | 4205 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 83),[(26942,4),(26943,1)]⟩
 | 4206 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 84),[(26944,1)]⟩
 | 4207 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 85),[(26945,1)]⟩
 | 4208 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 86),[(26947,1)]⟩
 | 4209 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 87),[(26946,4),(26947,1)]⟩
 | 4210 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 88),[(26948,1)]⟩
 | 4211 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 89),[(26949,1)]⟩
 | 4212 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 90),[(26951,1)]⟩
 | 4213 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 91),[(26950,4),(26951,1)]⟩
 | 4214 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 92),[(26952,1)]⟩
 | 4215 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 93),[(26953,1)]⟩
 | 4216 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 94),[(26955,1)]⟩
 | 4217 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 95),[(26954,4),(26955,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B13.count
