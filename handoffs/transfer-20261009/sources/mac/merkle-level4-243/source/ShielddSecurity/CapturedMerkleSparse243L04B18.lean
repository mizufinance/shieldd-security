import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0024
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5130 16
def localParent : Nat → Option Row
 | 5130 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 22),[(27868,1)]⟩
 | 5131 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 23),[(27869,1)]⟩
 | 5132 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 24),[(27871,1)]⟩
 | 5133 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 25),[(27870,4),(27871,1)]⟩
 | 5134 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 26),[(27872,1)]⟩
 | 5135 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 27),[(27873,1)]⟩
 | 5136 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 28),[(27875,1)]⟩
 | 5137 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 29),[(27874,4),(27875,1)]⟩
 | 5138 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 30),[(27876,1)]⟩
 | 5139 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 31),[(27877,1)]⟩
 | 5140 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 32),[(27879,1)]⟩
 | 5141 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 33),[(27878,4),(27879,1)]⟩
 | 5142 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 34),[(27880,1)]⟩
 | 5143 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 35),[(27881,1)]⟩
 | 5144 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 36),[(27883,1)]⟩
 | 5145 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 37),[(27882,4),(27883,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B18.count
