import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0044
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B08
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 76).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9210 16
def localParent : Nat → Option Row
 | 9210 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 34),[(31948,1)]⟩
 | 9211 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 35),[(31949,1)]⟩
 | 9212 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 36),[(31951,1)]⟩
 | 9213 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 37),[(31950,4),(31951,1)]⟩
 | 9214 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 38),[(31952,1)]⟩
 | 9215 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 39),[(31953,1)]⟩
 | 9216 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 40),[(31955,1)]⟩
 | 9217 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 41),[(31954,4),(31955,1)]⟩
 | 9218 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 42),[(31956,1)]⟩
 | 9219 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 43),[(31957,1)]⟩
 | 9220 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 44),[(31959,1)]⟩
 | 9221 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 45),[(31958,4),(31959,1)]⟩
 | 9222 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 46),[(31960,1)]⟩
 | 9223 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 47),[(31961,1)]⟩
 | 9224 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 48),[(31963,1)]⟩
 | 9225 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 49),[(31962,4),(31963,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B08

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B08.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B08.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B08.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B08.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B08.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B08.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B08.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B08.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B08.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B08.count
