import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0016
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B08
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 76).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3698 16
def localParent : Nat → Option Row
 | 3698 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 252),[(26436,1)]⟩
 | 3699 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 253),[(26437,1)]⟩
 | 3700 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 254),[(26439,1)]⟩
 | 3701 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 255),[(26438,4),(26439,1)]⟩
 | 3702 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 256),[(26440,1)]⟩
 | 3703 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 257),[(26441,1)]⟩
 | 3704 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 258),[(26443,1)]⟩
 | 3705 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 259),[(26442,4),(26443,1)]⟩
 | 3706 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 260),[(26444,1)]⟩
 | 3707 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 261),[(26445,1)]⟩
 | 3708 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 262),[(26447,1)]⟩
 | 3709 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 263),[(26446,4),(26447,1)]⟩
 | 3710 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 264),[(26448,1)]⟩
 | 3711 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 265),[(26449,1)]⟩
 | 3712 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 266),[(26451,1)]⟩
 | 3713 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0016.inputs 267),[(26450,4),(26451,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B08

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B08.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B08.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B08.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B08.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B08.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B08.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B08.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B08.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B08.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B08.count
