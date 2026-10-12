import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0024
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5178 16
def localParent : Nat → Option Row
 | 5178 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 70),[(27916,1)]⟩
 | 5179 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 71),[(27917,1)]⟩
 | 5180 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 72),[(27919,1)]⟩
 | 5181 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 73),[(27918,4),(27919,1)]⟩
 | 5182 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 74),[(27920,1)]⟩
 | 5183 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 75),[(27921,1)]⟩
 | 5184 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 76),[(27923,1)]⟩
 | 5185 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 77),[(27922,4),(27923,1)]⟩
 | 5186 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 78),[(27924,1)]⟩
 | 5187 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 79),[(27925,1)]⟩
 | 5188 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 80),[(27927,1)]⟩
 | 5189 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 81),[(27926,4),(27927,1)]⟩
 | 5190 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 82),[(27928,1)]⟩
 | 5191 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 83),[(27929,1)]⟩
 | 5192 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 84),[(27931,1)]⟩
 | 5193 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 85),[(27930,4),(27931,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B21.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B21.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B21.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B21.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B21.count
