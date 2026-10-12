import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5754 16
def localParent : Nat → Option Row
 | 5754 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 140),[(28492,1)]⟩
 | 5755 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 141),[(28493,1)]⟩
 | 5756 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 142),[(28495,1)]⟩
 | 5757 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 143),[(28494,4),(28495,1)]⟩
 | 5758 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 144),[(28496,1)]⟩
 | 5759 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 145),[(28497,1)]⟩
 | 5760 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 146),[(28499,1)]⟩
 | 5761 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 147),[(28498,4),(28499,1)]⟩
 | 5762 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 148),[(28500,1)]⟩
 | 5763 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 149),[(28501,1)]⟩
 | 5764 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 150),[(28503,1)]⟩
 | 5765 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 151),[(28502,4),(28503,1)]⟩
 | 5766 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 152),[(28504,1)]⟩
 | 5767 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 153),[(28505,1)]⟩
 | 5768 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 154),[(28507,1)]⟩
 | 5769 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 155),[(28506,4),(28507,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B04.count
