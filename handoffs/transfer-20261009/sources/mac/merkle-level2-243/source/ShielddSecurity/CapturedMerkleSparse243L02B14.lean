import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0019
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B14
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 172).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4218 16
def localParent : Nat → Option Row
 | 4218 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 96),[(26956,1)]⟩
 | 4219 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 97),[(26957,1)]⟩
 | 4220 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 98),[(26959,1)]⟩
 | 4221 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 99),[(26958,4),(26959,1)]⟩
 | 4222 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 100),[(26960,1)]⟩
 | 4223 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 101),[(26961,1)]⟩
 | 4224 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 102),[(26963,1)]⟩
 | 4225 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 103),[(26962,4),(26963,1)]⟩
 | 4226 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 104),[(26964,1)]⟩
 | 4227 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 105),[(26965,1)]⟩
 | 4228 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 106),[(26967,1)]⟩
 | 4229 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 107),[(26966,4),(26967,1)]⟩
 | 4230 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 108),[(26968,1)]⟩
 | 4231 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 109),[(26969,1)]⟩
 | 4232 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 110),[(26971,1)]⟩
 | 4233 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 111),[(26970,4),(26971,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B14

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B14.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B14.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B14.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B14.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B14.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B14.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B14.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B14.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B14.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B14.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B14.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B14.count
