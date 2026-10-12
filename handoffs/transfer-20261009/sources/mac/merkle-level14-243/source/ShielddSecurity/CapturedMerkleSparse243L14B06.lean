import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0044
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9178 16
def localParent : Nat → Option Row
 | 9178 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 2),[(31916,1)]⟩
 | 9179 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 3),[(31917,1)]⟩
 | 9180 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 4),[(31919,1)]⟩
 | 9181 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 5),[(31918,4),(31919,1)]⟩
 | 9182 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 6),[(31920,1)]⟩
 | 9183 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 7),[(31921,1)]⟩
 | 9184 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 8),[(31923,1)]⟩
 | 9185 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 9),[(31922,4),(31923,1)]⟩
 | 9186 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 10),[(31924,1)]⟩
 | 9187 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 11),[(31925,1)]⟩
 | 9188 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 12),[(31927,1)]⟩
 | 9189 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 13),[(31926,4),(31927,1)]⟩
 | 9190 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 14),[(31928,1)]⟩
 | 9191 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 15),[(31929,1)]⟩
 | 9192 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 16),[(31931,1)]⟩
 | 9193 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 17),[(31930,4),(31931,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B06.count
