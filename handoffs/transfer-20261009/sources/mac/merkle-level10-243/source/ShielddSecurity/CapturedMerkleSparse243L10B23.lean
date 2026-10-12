import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 316).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7754 16
def localParent : Nat → Option Row
 | 7754 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 58),[(30492,1)]⟩
 | 7755 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 59),[(30493,1)]⟩
 | 7756 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 60),[(30495,1)]⟩
 | 7757 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 61),[(30494,4),(30495,1)]⟩
 | 7758 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 62),[(30496,1)]⟩
 | 7759 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 63),[(30497,1)]⟩
 | 7760 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 64),[(30499,1)]⟩
 | 7761 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 65),[(30498,4),(30499,1)]⟩
 | 7762 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 66),[(30500,1)]⟩
 | 7763 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 67),[(30501,1)]⟩
 | 7764 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 68),[(30503,1)]⟩
 | 7765 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 69),[(30502,4),(30503,1)]⟩
 | 7766 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 70),[(30504,1)]⟩
 | 7767 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 71),[(30505,1)]⟩
 | 7768 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 72),[(30507,1)]⟩
 | 7769 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 73),[(30506,4),(30507,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B23.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B23.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B23.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B23.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B23.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B23.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B23.count
