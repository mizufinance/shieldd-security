import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5442 16
def localParent : Nat → Option Row
 | 5442 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 222),[(28180,1)]⟩
 | 5443 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 223),[(28181,1)]⟩
 | 5444 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 224),[(28183,1)]⟩
 | 5445 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 225),[(28182,4),(28183,1)]⟩
 | 5446 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 226),[(28184,1)]⟩
 | 5447 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 227),[(28185,1)]⟩
 | 5448 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 228),[(28187,1)]⟩
 | 5449 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 229),[(28186,4),(28187,1)]⟩
 | 5450 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 230),[(28188,1)]⟩
 | 5451 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 231),[(28189,1)]⟩
 | 5452 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 232),[(28191,1)]⟩
 | 5453 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 233),[(28190,4),(28191,1)]⟩
 | 5454 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 234),[(28192,1)]⟩
 | 5455 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 235),[(28193,1)]⟩
 | 5456 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 236),[(28195,1)]⟩
 | 5457 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 237),[(28194,4),(28195,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B11.count
