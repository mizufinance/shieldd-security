import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5226 16
def localParent : Nat → Option Row
 | 5226 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 6),[(27964,1)]⟩
 | 5227 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 7),[(27965,1)]⟩
 | 5228 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 8),[(27967,1)]⟩
 | 5229 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 9),[(27966,4),(27967,1)]⟩
 | 5230 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 10),[(27968,1)]⟩
 | 5231 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 11),[(27969,1)]⟩
 | 5232 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 12),[(27971,1)]⟩
 | 5233 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 13),[(27970,4),(27971,1)]⟩
 | 5234 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 14),[(27972,1)]⟩
 | 5235 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 15),[(27973,1)]⟩
 | 5236 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 16),[(27975,1)]⟩
 | 5237 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 17),[(27974,4),(27975,1)]⟩
 | 5238 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 18),[(27976,1)]⟩
 | 5239 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 19),[(27977,1)]⟩
 | 5240 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 20),[(27979,1)]⟩
 | 5241 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 21),[(27978,4),(27979,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B24.count
