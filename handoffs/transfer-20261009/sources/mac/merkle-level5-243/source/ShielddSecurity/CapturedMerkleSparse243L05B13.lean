import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5474 16
def localParent : Nat → Option Row
 | 5474 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 254),[(28212,1)]⟩
 | 5475 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 255),[(28213,1)]⟩
 | 5476 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 256),[(28215,1)]⟩
 | 5477 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 257),[(28214,4),(28215,1)]⟩
 | 5478 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 258),[(28216,1)]⟩
 | 5479 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 259),[(28217,1)]⟩
 | 5480 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 260),[(28219,1)]⟩
 | 5481 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 261),[(28218,4),(28219,1)]⟩
 | 5482 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 262),[(28220,1)]⟩
 | 5483 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 263),[(28221,1)]⟩
 | 5484 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 264),[(28223,1)]⟩
 | 5485 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 265),[(28222,4),(28223,1)]⟩
 | 5486 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 266),[(28224,1)]⟩
 | 5487 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 267),[(28225,1)]⟩
 | 5488 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 268),[(28227,1)]⟩
 | 5489 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 269),[(28226,4),(28227,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B13.count
