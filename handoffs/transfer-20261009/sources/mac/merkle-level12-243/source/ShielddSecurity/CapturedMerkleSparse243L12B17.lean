import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0040
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8506 16
def localParent : Nat → Option Row
 | 8506 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 115),[(31244,1)]⟩
 | 8507 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 116),[(31245,1)]⟩
 | 8508 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 117),[(31247,1)]⟩
 | 8509 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 118),[(31246,4),(31247,1)]⟩
 | 8510 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 119),[(31248,1)]⟩
 | 8511 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 120),[(31249,1)]⟩
 | 8512 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 121),[(31251,1)]⟩
 | 8513 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 122),[(31250,4),(31251,1)]⟩
 | 8514 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 123),[(31252,1)]⟩
 | 8515 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 124),[(31253,1)]⟩
 | 8516 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 125),[(31255,1)]⟩
 | 8517 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 126),[(31254,4),(31255,1)]⟩
 | 8518 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 127),[(31256,1)]⟩
 | 8519 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 128),[(31257,1)]⟩
 | 8520 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 129),[(31259,1)]⟩
 | 8521 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 130),[(31258,4),(31259,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B17.count
