import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0023
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5034 16
def localParent : Nat → Option Row
 | 5034 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 170),[(27772,1)]⟩
 | 5035 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 171),[(27773,1)]⟩
 | 5036 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 172),[(27775,1)]⟩
 | 5037 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 173),[(27774,4),(27775,1)]⟩
 | 5038 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 174),[(27776,1)]⟩
 | 5039 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 175),[(27777,1)]⟩
 | 5040 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 176),[(27779,1)]⟩
 | 5041 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 177),[(27778,4),(27779,1)]⟩
 | 5042 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 178),[(27780,1)]⟩
 | 5043 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 179),[(27781,1)]⟩
 | 5044 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 180),[(27783,1)]⟩
 | 5045 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 181),[(27782,4),(27783,1)]⟩
 | 5046 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 182),[(27784,1)]⟩
 | 5047 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 183),[(27785,1)]⟩
 | 5048 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 184),[(27787,1)]⟩
 | 5049 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 185),[(27786,4),(27787,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B12.count
