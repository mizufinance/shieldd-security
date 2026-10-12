import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0044
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9242 16
def localParent : Nat → Option Row
 | 9242 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 66),[(31980,1)]⟩
 | 9243 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 67),[(31981,1)]⟩
 | 9244 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 68),[(31983,1)]⟩
 | 9245 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 69),[(31982,4),(31983,1)]⟩
 | 9246 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 70),[(31984,1)]⟩
 | 9247 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 71),[(31985,1)]⟩
 | 9248 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 72),[(31987,1)]⟩
 | 9249 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 73),[(31986,4),(31987,1)]⟩
 | 9250 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 74),[(31988,1)]⟩
 | 9251 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 75),[(31989,1)]⟩
 | 9252 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 76),[(31991,1)]⟩
 | 9253 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 77),[(31990,4),(31991,1)]⟩
 | 9254 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 78),[(31992,1)]⟩
 | 9255 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 79),[(31993,1)]⟩
 | 9256 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 80),[(31995,1)]⟩
 | 9257 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 81),[(31994,4),(31995,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B10.count
