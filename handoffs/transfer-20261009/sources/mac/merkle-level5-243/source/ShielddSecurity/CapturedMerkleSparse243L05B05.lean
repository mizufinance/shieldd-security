import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5346 16
def localParent : Nat → Option Row
 | 5346 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 126),[(28084,1)]⟩
 | 5347 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 127),[(28085,1)]⟩
 | 5348 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 128),[(28087,1)]⟩
 | 5349 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 129),[(28086,4),(28087,1)]⟩
 | 5350 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 130),[(28088,1)]⟩
 | 5351 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 131),[(28089,1)]⟩
 | 5352 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 132),[(28091,1)]⟩
 | 5353 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 133),[(28090,4),(28091,1)]⟩
 | 5354 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 134),[(28092,1)]⟩
 | 5355 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 135),[(28093,1)]⟩
 | 5356 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 136),[(28095,1)]⟩
 | 5357 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 137),[(28094,4),(28095,1)]⟩
 | 5358 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 138),[(28096,1)]⟩
 | 5359 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 139),[(28097,1)]⟩
 | 5360 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 140),[(28099,1)]⟩
 | 5361 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 141),[(28098,4),(28099,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B05.count
