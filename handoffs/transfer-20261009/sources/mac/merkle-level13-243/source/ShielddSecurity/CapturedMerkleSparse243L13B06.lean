import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0041
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8754 16
def localParent : Nat → Option Row
 | 8754 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 226),[(31492,1)]⟩
 | 8755 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 227),[(31493,1)]⟩
 | 8756 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 228),[(31495,1)]⟩
 | 8757 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 229),[(31494,4),(31495,1)]⟩
 | 8758 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 230),[(31496,1)]⟩
 | 8759 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 231),[(31497,1)]⟩
 | 8760 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 232),[(31499,1)]⟩
 | 8761 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 233),[(31498,4),(31499,1)]⟩
 | 8762 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 234),[(31500,1)]⟩
 | 8763 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 235),[(31501,1)]⟩
 | 8764 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 236),[(31503,1)]⟩
 | 8765 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 237),[(31502,4),(31503,1)]⟩
 | 8766 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 238),[(31504,1)]⟩
 | 8767 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 239),[(31505,1)]⟩
 | 8768 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 240),[(31507,1)]⟩
 | 8769 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 241),[(31506,4),(31507,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B06.count
