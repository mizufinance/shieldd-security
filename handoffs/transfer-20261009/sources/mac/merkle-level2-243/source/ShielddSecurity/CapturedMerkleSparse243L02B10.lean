import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0019
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4154 16
def localParent : Nat → Option Row
 | 4154 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 32),[(26892,1)]⟩
 | 4155 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 33),[(26893,1)]⟩
 | 4156 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 34),[(26895,1)]⟩
 | 4157 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 35),[(26894,4),(26895,1)]⟩
 | 4158 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 36),[(26896,1)]⟩
 | 4159 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 37),[(26897,1)]⟩
 | 4160 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 38),[(26899,1)]⟩
 | 4161 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 39),[(26898,4),(26899,1)]⟩
 | 4162 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 40),[(26900,1)]⟩
 | 4163 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 41),[(26901,1)]⟩
 | 4164 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 42),[(26903,1)]⟩
 | 4165 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 43),[(26902,4),(26903,1)]⟩
 | 4166 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 44),[(26904,1)]⟩
 | 4167 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 45),[(26905,1)]⟩
 | 4168 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 46),[(26907,1)]⟩
 | 4169 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 47),[(26906,4),(26907,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B10.count
