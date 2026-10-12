import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0018
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4058 16
def localParent : Nat → Option Row
 | 4058 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 196),[(26796,1)]⟩
 | 4059 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 197),[(26797,1)]⟩
 | 4060 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 198),[(26799,1)]⟩
 | 4061 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 199),[(26798,4),(26799,1)]⟩
 | 4062 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 200),[(26800,1)]⟩
 | 4063 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 201),[(26801,1)]⟩
 | 4064 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 202),[(26803,1)]⟩
 | 4065 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 203),[(26802,4),(26803,1)]⟩
 | 4066 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 204),[(26804,1)]⟩
 | 4067 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 205),[(26805,1)]⟩
 | 4068 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 206),[(26807,1)]⟩
 | 4069 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 207),[(26806,4),(26807,1)]⟩
 | 4070 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 208),[(26808,1)]⟩
 | 4071 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 209),[(26809,1)]⟩
 | 4072 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 210),[(26811,1)]⟩
 | 4073 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 211),[(26810,4),(26811,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B04.count
