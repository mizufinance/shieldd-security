import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0018
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4074 16
def localParent : Nat → Option Row
 | 4074 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 212),[(26812,1)]⟩
 | 4075 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 213),[(26813,1)]⟩
 | 4076 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 214),[(26815,1)]⟩
 | 4077 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 215),[(26814,4),(26815,1)]⟩
 | 4078 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 216),[(26816,1)]⟩
 | 4079 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 217),[(26817,1)]⟩
 | 4080 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 218),[(26819,1)]⟩
 | 4081 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 219),[(26818,4),(26819,1)]⟩
 | 4082 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 220),[(26820,1)]⟩
 | 4083 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 221),[(26821,1)]⟩
 | 4084 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 222),[(26823,1)]⟩
 | 4085 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 223),[(26822,4),(26823,1)]⟩
 | 4086 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 224),[(26824,1)]⟩
 | 4087 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 225),[(26825,1)]⟩
 | 4088 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 226),[(26827,1)]⟩
 | 4089 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 227),[(26826,4),(26827,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B05.count
