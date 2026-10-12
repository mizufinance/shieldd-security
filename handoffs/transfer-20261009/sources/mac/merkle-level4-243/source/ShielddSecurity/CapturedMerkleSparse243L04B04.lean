import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0023
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4906 16
def localParent : Nat → Option Row
 | 4906 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 42),[(27644,1)]⟩
 | 4907 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 43),[(27645,1)]⟩
 | 4908 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 44),[(27647,1)]⟩
 | 4909 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 45),[(27646,4),(27647,1)]⟩
 | 4910 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 46),[(27648,1)]⟩
 | 4911 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 47),[(27649,1)]⟩
 | 4912 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 48),[(27651,1)]⟩
 | 4913 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 49),[(27650,4),(27651,1)]⟩
 | 4914 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 50),[(27652,1)]⟩
 | 4915 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 51),[(27653,1)]⟩
 | 4916 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 52),[(27655,1)]⟩
 | 4917 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 53),[(27654,4),(27655,1)]⟩
 | 4918 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 54),[(27656,1)]⟩
 | 4919 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 55),[(27657,1)]⟩
 | 4920 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 56),[(27659,1)]⟩
 | 4921 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 57),[(27658,4),(27659,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B04.count
