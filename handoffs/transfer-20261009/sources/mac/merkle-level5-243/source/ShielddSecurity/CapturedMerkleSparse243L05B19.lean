import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0026
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5570 16
def localParent : Nat → Option Row
 | 5570 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 48),[(28308,1)]⟩
 | 5571 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 49),[(28309,1)]⟩
 | 5572 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 50),[(28311,1)]⟩
 | 5573 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 51),[(28310,4),(28311,1)]⟩
 | 5574 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 52),[(28312,1)]⟩
 | 5575 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 53),[(28313,1)]⟩
 | 5576 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 54),[(28315,1)]⟩
 | 5577 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 55),[(28314,4),(28315,1)]⟩
 | 5578 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 56),[(28316,1)]⟩
 | 5579 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 57),[(28317,1)]⟩
 | 5580 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 58),[(28319,1)]⟩
 | 5581 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 59),[(28318,4),(28319,1)]⟩
 | 5582 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 60),[(28320,1)]⟩
 | 5583 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 61),[(28321,1)]⟩
 | 5584 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 62),[(28323,1)]⟩
 | 5585 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 63),[(28322,4),(28323,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B19.count
