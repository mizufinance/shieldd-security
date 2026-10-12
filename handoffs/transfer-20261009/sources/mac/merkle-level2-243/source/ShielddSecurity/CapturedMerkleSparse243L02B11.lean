import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0019
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4170 16
def localParent : Nat → Option Row
 | 4170 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 48),[(26908,1)]⟩
 | 4171 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 49),[(26909,1)]⟩
 | 4172 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 50),[(26911,1)]⟩
 | 4173 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 51),[(26910,4),(26911,1)]⟩
 | 4174 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 52),[(26912,1)]⟩
 | 4175 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 53),[(26913,1)]⟩
 | 4176 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 54),[(26915,1)]⟩
 | 4177 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 55),[(26914,4),(26915,1)]⟩
 | 4178 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 56),[(26916,1)]⟩
 | 4179 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 57),[(26917,1)]⟩
 | 4180 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 58),[(26919,1)]⟩
 | 4181 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 59),[(26918,4),(26919,1)]⟩
 | 4182 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 60),[(26920,1)]⟩
 | 4183 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 61),[(26921,1)]⟩
 | 4184 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 62),[(26923,1)]⟩
 | 4185 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 63),[(26922,4),(26923,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B11.count
