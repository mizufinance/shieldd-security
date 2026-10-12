import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0020
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4314 16
def localParent : Nat → Option Row
 | 4314 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 36),[(27052,1)]⟩
 | 4315 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 37),[(27053,1)]⟩
 | 4316 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 38),[(27055,1)]⟩
 | 4317 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 39),[(27054,4),(27055,1)]⟩
 | 4318 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 40),[(27056,1)]⟩
 | 4319 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 41),[(27057,1)]⟩
 | 4320 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 42),[(27059,1)]⟩
 | 4321 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 43),[(27058,4),(27059,1)]⟩
 | 4322 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 44),[(27060,1)]⟩
 | 4323 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 45),[(27061,1)]⟩
 | 4324 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 46),[(27063,1)]⟩
 | 4325 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 47),[(27062,4),(27063,1)]⟩
 | 4326 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 48),[(27064,1)]⟩
 | 4327 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 49),[(27065,1)]⟩
 | 4328 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 50),[(27067,1)]⟩
 | 4329 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 51),[(27066,4),(27067,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B20.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B20.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B20.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B20.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B20.count
