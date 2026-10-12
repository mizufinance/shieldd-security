import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0024
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5162 16
def localParent : Nat → Option Row
 | 5162 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 54),[(27900,1)]⟩
 | 5163 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 55),[(27901,1)]⟩
 | 5164 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 56),[(27903,1)]⟩
 | 5165 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 57),[(27902,4),(27903,1)]⟩
 | 5166 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 58),[(27904,1)]⟩
 | 5167 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 59),[(27905,1)]⟩
 | 5168 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 60),[(27907,1)]⟩
 | 5169 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 61),[(27906,4),(27907,1)]⟩
 | 5170 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 62),[(27908,1)]⟩
 | 5171 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 63),[(27909,1)]⟩
 | 5172 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 64),[(27911,1)]⟩
 | 5173 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 65),[(27910,4),(27911,1)]⟩
 | 5174 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 66),[(27912,1)]⟩
 | 5175 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 67),[(27913,1)]⟩
 | 5176 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 68),[(27915,1)]⟩
 | 5177 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 69),[(27914,4),(27915,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B20.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B20.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B20.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B20.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B20.count
