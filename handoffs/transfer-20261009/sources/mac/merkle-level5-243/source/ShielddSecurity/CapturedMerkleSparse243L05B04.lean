import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0025
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5330 16
def localParent : Nat → Option Row
 | 5330 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 110),[(28068,1)]⟩
 | 5331 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 111),[(28069,1)]⟩
 | 5332 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 112),[(28071,1)]⟩
 | 5333 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 113),[(28070,4),(28071,1)]⟩
 | 5334 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 114),[(28072,1)]⟩
 | 5335 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 115),[(28073,1)]⟩
 | 5336 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 116),[(28075,1)]⟩
 | 5337 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 117),[(28074,4),(28075,1)]⟩
 | 5338 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 118),[(28076,1)]⟩
 | 5339 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 119),[(28077,1)]⟩
 | 5340 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 120),[(28079,1)]⟩
 | 5341 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 121),[(28078,4),(28079,1)]⟩
 | 5342 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 122),[(28080,1)]⟩
 | 5343 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 123),[(28081,1)]⟩
 | 5344 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 124),[(28083,1)]⟩
 | 5345 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0025.inputs 125),[(28082,4),(28083,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B04.count
