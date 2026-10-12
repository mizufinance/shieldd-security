import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B14
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 172).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5490 16
def localParent : Nat → Option Row
 | 5490 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 270),[(28228,1)]⟩
 | 5491 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 271),[(28229,1)]⟩
 | 5492 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 272),[(28231,1)]⟩
 | 5493 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 273),[(28230,4),(28231,1)]⟩
 | 5494 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 274),[(28232,1)]⟩
 | 5495 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 275),[(28233,1)]⟩
 | 5496 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 276),[(28235,1)]⟩
 | 5497 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 277),[(28234,4),(28235,1)]⟩
 | 5498 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 278),[(28236,1)]⟩
 | 5499 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 279),[(28237,1)]⟩
 | 5500 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 280),[(28239,1)]⟩
 | 5501 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 281),[(28238,4),(28239,1)]⟩
 | 5502 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 282),[(28240,1)]⟩
 | 5503 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 283),[(28241,1)]⟩
 | 5504 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 284),[(28243,1)]⟩
 | 5505 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 285),[(28242,4),(28243,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B14

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B14.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B14.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B14.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B14.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B14.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B14.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B14.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B14.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B14.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B14.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B14.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B14.count
