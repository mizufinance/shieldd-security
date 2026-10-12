import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0039
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B08
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 76).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8362 16
def localParent : Nat → Option Row
 | 8362 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 250),[(31100,1)]⟩
 | 8363 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 251),[(31101,1)]⟩
 | 8364 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 252),[(31103,1)]⟩
 | 8365 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 253),[(31102,4),(31103,1)]⟩
 | 8366 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 254),[(31104,1)]⟩
 | 8367 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 255),[(31105,1)]⟩
 | 8368 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 256),[(31107,1)]⟩
 | 8369 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 257),[(31106,4),(31107,1)]⟩
 | 8370 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 258),[(31108,1)]⟩
 | 8371 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 259),[(31109,1)]⟩
 | 8372 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 260),[(31111,1)]⟩
 | 8373 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 261),[(31110,4),(31111,1)]⟩
 | 8374 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 262),[(31112,1)]⟩
 | 8375 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 263),[(31113,1)]⟩
 | 8376 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 264),[(31115,1)]⟩
 | 8377 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0039.inputs 265),[(31114,4),(31115,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B08

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B08.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B08.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B08.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B08.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B08.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B08.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B08.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B08.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B08.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B08.count
