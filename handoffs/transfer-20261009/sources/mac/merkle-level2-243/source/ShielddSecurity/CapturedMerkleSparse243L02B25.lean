import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0020
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4394 16
def localParent : Nat → Option Row
 | 4394 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 116),[(27132,1)]⟩
 | 4395 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 117),[(27133,1)]⟩
 | 4396 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 118),[(27135,1)]⟩
 | 4397 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 119),[(27134,4),(27135,1)]⟩
 | 4398 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 120),[(27136,1)]⟩
 | 4399 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 121),[(27137,1)]⟩
 | 4400 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 122),[(27139,1)]⟩
 | 4401 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 123),[(27138,4),(27139,1)]⟩
 | 4402 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 124),[(27140,1)]⟩
 | 4403 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 125),[(27141,1)]⟩
 | 4404 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 126),[(27143,1)]⟩
 | 4405 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 127),[(27142,4),(27143,1)]⟩
 | 4406 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 128),[(27144,1)]⟩
 | 4407 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 129),[(27145,1)]⟩
 | 4408 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 130),[(27147,1)]⟩
 | 4409 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0020.inputs 131),[(27146,4),(27147,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B25.count
