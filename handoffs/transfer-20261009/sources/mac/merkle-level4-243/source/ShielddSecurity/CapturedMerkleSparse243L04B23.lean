import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0024
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 316).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5210 16
def localParent : Nat → Option Row
 | 5210 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 102),[(27948,1)]⟩
 | 5211 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 103),[(27949,1)]⟩
 | 5212 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 104),[(27951,1)]⟩
 | 5213 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 105),[(27950,4),(27951,1)]⟩
 | 5214 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 106),[(27952,1)]⟩
 | 5215 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 107),[(27953,1)]⟩
 | 5216 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 108),[(27955,1)]⟩
 | 5217 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 109),[(27954,4),(27955,1)]⟩
 | 5218 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 110),[(27956,1)]⟩
 | 5219 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0024.inputs 111),[(27957,1)]⟩
 | 5220 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 0),[(27959,1)]⟩
 | 5221 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 1),[(27958,4),(27959,1)]⟩
 | 5222 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 2),[(27960,1)]⟩
 | 5223 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 3),[(27961,1)]⟩
 | 5224 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 4),[(27963,1)]⟩
 | 5225 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 5),[(27962,4),(27963,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B23.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B23.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B23.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B23.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B23.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B23.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B23.count
