import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0024
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5114 16
def localParent : Nat → Option Row
 | 5114 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 6),[(27852,1)]⟩
 | 5115 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 7),[(27853,1)]⟩
 | 5116 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 8),[(27855,1)]⟩
 | 5117 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 9),[(27854,4),(27855,1)]⟩
 | 5118 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 10),[(27856,1)]⟩
 | 5119 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 11),[(27857,1)]⟩
 | 5120 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 12),[(27859,1)]⟩
 | 5121 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 13),[(27858,4),(27859,1)]⟩
 | 5122 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 14),[(27860,1)]⟩
 | 5123 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 15),[(27861,1)]⟩
 | 5124 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 16),[(27863,1)]⟩
 | 5125 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 17),[(27862,4),(27863,1)]⟩
 | 5126 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 18),[(27864,1)]⟩
 | 5127 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 19),[(27865,1)]⟩
 | 5128 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 20),[(27867,1)]⟩
 | 5129 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 21),[(27866,4),(27867,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B17.count
