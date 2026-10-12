import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0023
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5082 16
def localParent : Nat → Option Row
 | 5082 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 218),[(27820,1)]⟩
 | 5083 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 219),[(27821,1)]⟩
 | 5084 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 220),[(27823,1)]⟩
 | 5085 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 221),[(27822,4),(27823,1)]⟩
 | 5086 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 222),[(27824,1)]⟩
 | 5087 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 223),[(27825,1)]⟩
 | 5088 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 224),[(27827,1)]⟩
 | 5089 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 225),[(27826,4),(27827,1)]⟩
 | 5090 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 226),[(27828,1)]⟩
 | 5091 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 227),[(27829,1)]⟩
 | 5092 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 228),[(27831,1)]⟩
 | 5093 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 229),[(27830,4),(27831,1)]⟩
 | 5094 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 230),[(27832,1)]⟩
 | 5095 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 231),[(27833,1)]⟩
 | 5096 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 232),[(27835,1)]⟩
 | 5097 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 233),[(27834,4),(27835,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B15.count
