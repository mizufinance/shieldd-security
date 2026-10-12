import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0024
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 300).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5194 16
def localParent : Nat → Option Row
 | 5194 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 86),[(27932,1)]⟩
 | 5195 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 87),[(27933,1)]⟩
 | 5196 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 88),[(27935,1)]⟩
 | 5197 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 89),[(27934,4),(27935,1)]⟩
 | 5198 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 90),[(27936,1)]⟩
 | 5199 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 91),[(27937,1)]⟩
 | 5200 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 92),[(27939,1)]⟩
 | 5201 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 93),[(27938,4),(27939,1)]⟩
 | 5202 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 94),[(27940,1)]⟩
 | 5203 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 95),[(27941,1)]⟩
 | 5204 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 96),[(27943,1)]⟩
 | 5205 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 97),[(27942,4),(27943,1)]⟩
 | 5206 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 98),[(27944,1)]⟩
 | 5207 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 99),[(27945,1)]⟩
 | 5208 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 100),[(27947,1)]⟩
 | 5209 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 101),[(27946,4),(27947,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B22.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B22.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B22.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B22.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B22.count
