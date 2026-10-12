import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0044
import ShielddSecurity.CapturedArithmetic45B0045
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9354 16
def localParent : Nat → Option Row
 | 9354 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 178),[(32092,1)]⟩
 | 9355 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 179),[(32093,1)]⟩
 | 9356 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 180),[(32095,1)]⟩
 | 9357 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 181),[(32094,4),(32095,1)]⟩
 | 9358 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 182),[(32096,1)]⟩
 | 9359 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 183),[(32097,1)]⟩
 | 9360 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 0),[(32099,1)]⟩
 | 9361 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 1),[(32098,4),(32099,1)]⟩
 | 9362 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 2),[(32100,1)]⟩
 | 9363 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 3),[(32101,1)]⟩
 | 9364 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 4),[(32103,1)]⟩
 | 9365 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 5),[(32102,4),(32103,1)]⟩
 | 9366 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 6),[(32104,1)]⟩
 | 9367 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 7),[(32105,1)]⟩
 | 9368 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 8),[(32107,1)]⟩
 | 9369 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 9),[(32106,4),(32107,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B17.count
