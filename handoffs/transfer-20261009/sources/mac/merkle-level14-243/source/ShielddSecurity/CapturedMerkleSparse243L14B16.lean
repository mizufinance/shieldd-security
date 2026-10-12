import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0044
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9338 16
def localParent : Nat → Option Row
 | 9338 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 162),[(32076,1)]⟩
 | 9339 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 163),[(32077,1)]⟩
 | 9340 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 164),[(32079,1)]⟩
 | 9341 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 165),[(32078,4),(32079,1)]⟩
 | 9342 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 166),[(32080,1)]⟩
 | 9343 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 167),[(32081,1)]⟩
 | 9344 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 168),[(32083,1)]⟩
 | 9345 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 169),[(32082,4),(32083,1)]⟩
 | 9346 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 170),[(32084,1)]⟩
 | 9347 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 171),[(32085,1)]⟩
 | 9348 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 172),[(32087,1)]⟩
 | 9349 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 173),[(32086,4),(32087,1)]⟩
 | 9350 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 174),[(32088,1)]⟩
 | 9351 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 175),[(32089,1)]⟩
 | 9352 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 176),[(32091,1)]⟩
 | 9353 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 177),[(32090,4),(32091,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B16.count
