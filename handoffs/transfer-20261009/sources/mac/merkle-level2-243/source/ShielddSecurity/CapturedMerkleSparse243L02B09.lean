import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0019
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B09
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 92).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4138 16
def localParent : Nat → Option Row
 | 4138 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 16),[(26876,1)]⟩
 | 4139 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 17),[(26877,1)]⟩
 | 4140 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 18),[(26879,1)]⟩
 | 4141 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 19),[(26878,4),(26879,1)]⟩
 | 4142 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 20),[(26880,1)]⟩
 | 4143 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 21),[(26881,1)]⟩
 | 4144 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 22),[(26883,1)]⟩
 | 4145 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 23),[(26882,4),(26883,1)]⟩
 | 4146 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 24),[(26884,1)]⟩
 | 4147 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 25),[(26885,1)]⟩
 | 4148 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 26),[(26887,1)]⟩
 | 4149 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 27),[(26886,4),(26887,1)]⟩
 | 4150 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 28),[(26888,1)]⟩
 | 4151 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 29),[(26889,1)]⟩
 | 4152 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 30),[(26891,1)]⟩
 | 4153 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 31),[(26890,4),(26891,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B09.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B09.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B09.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B09.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B09.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B09.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B09.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B09.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B09.count
