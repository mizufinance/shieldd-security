import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0022
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4802 16
def localParent : Nat → Option Row
 | 4802 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 108),[(27540,1)]⟩
 | 4803 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 109),[(27541,1)]⟩
 | 4804 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 110),[(27543,1)]⟩
 | 4805 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 111),[(27542,4),(27543,1)]⟩
 | 4806 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 112),[(27544,1)]⟩
 | 4807 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 113),[(27545,1)]⟩
 | 4808 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 114),[(27547,1)]⟩
 | 4809 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 115),[(27546,4),(27547,1)]⟩
 | 4810 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 116),[(27548,1)]⟩
 | 4811 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 117),[(27549,1)]⟩
 | 4812 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 118),[(27551,1)]⟩
 | 4813 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 119),[(27550,4),(27551,1)]⟩
 | 4814 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 120),[(27552,1)]⟩
 | 4815 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 121),[(27553,1)]⟩
 | 4816 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 122),[(27555,1)]⟩
 | 4817 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 123),[(27554,4),(27555,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B24.count
