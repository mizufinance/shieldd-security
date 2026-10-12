import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0023
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5018 16
def localParent : Nat → Option Row
 | 5018 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 154),[(27756,1)]⟩
 | 5019 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 155),[(27757,1)]⟩
 | 5020 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 156),[(27759,1)]⟩
 | 5021 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 157),[(27758,4),(27759,1)]⟩
 | 5022 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 158),[(27760,1)]⟩
 | 5023 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 159),[(27761,1)]⟩
 | 5024 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 160),[(27763,1)]⟩
 | 5025 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 161),[(27762,4),(27763,1)]⟩
 | 5026 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 162),[(27764,1)]⟩
 | 5027 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 163),[(27765,1)]⟩
 | 5028 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 164),[(27767,1)]⟩
 | 5029 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 165),[(27766,4),(27767,1)]⟩
 | 5030 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 166),[(27768,1)]⟩
 | 5031 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 167),[(27769,1)]⟩
 | 5032 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 168),[(27771,1)]⟩
 | 5033 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 169),[(27770,4),(27771,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B11.count
