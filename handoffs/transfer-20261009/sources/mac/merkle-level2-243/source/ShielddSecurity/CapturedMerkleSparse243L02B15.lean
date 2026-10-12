import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0019
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4234 16
def localParent : Nat → Option Row
 | 4234 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 112),[(26972,1)]⟩
 | 4235 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 113),[(26973,1)]⟩
 | 4236 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 114),[(26975,1)]⟩
 | 4237 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 115),[(26974,4),(26975,1)]⟩
 | 4238 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 116),[(26976,1)]⟩
 | 4239 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 117),[(26977,1)]⟩
 | 4240 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 118),[(26979,1)]⟩
 | 4241 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 119),[(26978,4),(26979,1)]⟩
 | 4242 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 120),[(26980,1)]⟩
 | 4243 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 121),[(26981,1)]⟩
 | 4244 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 122),[(26983,1)]⟩
 | 4245 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 123),[(26982,4),(26983,1)]⟩
 | 4246 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 124),[(26984,1)]⟩
 | 4247 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 125),[(26985,1)]⟩
 | 4248 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 126),[(26987,1)]⟩
 | 4249 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 127),[(26986,4),(26987,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B15.count
