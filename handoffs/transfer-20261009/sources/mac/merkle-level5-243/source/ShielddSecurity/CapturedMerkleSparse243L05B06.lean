import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5362 16
def localParent : Nat → Option Row
 | 5362 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 142),[(28100,1)]⟩
 | 5363 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 143),[(28101,1)]⟩
 | 5364 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 144),[(28103,1)]⟩
 | 5365 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 145),[(28102,4),(28103,1)]⟩
 | 5366 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 146),[(28104,1)]⟩
 | 5367 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 147),[(28105,1)]⟩
 | 5368 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 148),[(28107,1)]⟩
 | 5369 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 149),[(28106,4),(28107,1)]⟩
 | 5370 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 150),[(28108,1)]⟩
 | 5371 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 151),[(28109,1)]⟩
 | 5372 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 152),[(28111,1)]⟩
 | 5373 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 153),[(28110,4),(28111,1)]⟩
 | 5374 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 154),[(28112,1)]⟩
 | 5375 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 155),[(28113,1)]⟩
 | 5376 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 156),[(28115,1)]⟩
 | 5377 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 157),[(28114,4),(28115,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B06.count
