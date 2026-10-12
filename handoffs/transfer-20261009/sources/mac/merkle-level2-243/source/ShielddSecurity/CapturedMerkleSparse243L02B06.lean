import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0018
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4090 16
def localParent : Nat → Option Row
 | 4090 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 228),[(26828,1)]⟩
 | 4091 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 229),[(26829,1)]⟩
 | 4092 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 230),[(26831,1)]⟩
 | 4093 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 231),[(26830,4),(26831,1)]⟩
 | 4094 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 232),[(26832,1)]⟩
 | 4095 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 233),[(26833,1)]⟩
 | 4096 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 234),[(26835,1)]⟩
 | 4097 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 235),[(26834,4),(26835,1)]⟩
 | 4098 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 236),[(26836,1)]⟩
 | 4099 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 237),[(26837,1)]⟩
 | 4100 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 238),[(26839,1)]⟩
 | 4101 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 239),[(26838,4),(26839,1)]⟩
 | 4102 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 240),[(26840,1)]⟩
 | 4103 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 241),[(26841,1)]⟩
 | 4104 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 242),[(26843,1)]⟩
 | 4105 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 243),[(26842,4),(26843,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B06.count
