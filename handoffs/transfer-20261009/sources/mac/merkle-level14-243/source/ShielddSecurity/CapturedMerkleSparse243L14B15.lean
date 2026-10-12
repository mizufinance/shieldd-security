import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0044
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9322 16
def localParent : Nat → Option Row
 | 9322 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 146),[(32060,1)]⟩
 | 9323 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 147),[(32061,1)]⟩
 | 9324 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 148),[(32063,1)]⟩
 | 9325 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 149),[(32062,4),(32063,1)]⟩
 | 9326 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 150),[(32064,1)]⟩
 | 9327 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 151),[(32065,1)]⟩
 | 9328 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 152),[(32067,1)]⟩
 | 9329 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 153),[(32066,4),(32067,1)]⟩
 | 9330 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 154),[(32068,1)]⟩
 | 9331 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 155),[(32069,1)]⟩
 | 9332 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 156),[(32071,1)]⟩
 | 9333 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 157),[(32070,4),(32071,1)]⟩
 | 9334 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 158),[(32072,1)]⟩
 | 9335 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 159),[(32073,1)]⟩
 | 9336 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 160),[(32075,1)]⟩
 | 9337 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 161),[(32074,4),(32075,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B15.count
