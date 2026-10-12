import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0044
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9274 16
def localParent : Nat → Option Row
 | 9274 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 98),[(32012,1)]⟩
 | 9275 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 99),[(32013,1)]⟩
 | 9276 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 100),[(32015,1)]⟩
 | 9277 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 101),[(32014,4),(32015,1)]⟩
 | 9278 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 102),[(32016,1)]⟩
 | 9279 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 103),[(32017,1)]⟩
 | 9280 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 104),[(32019,1)]⟩
 | 9281 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 105),[(32018,4),(32019,1)]⟩
 | 9282 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 106),[(32020,1)]⟩
 | 9283 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 107),[(32021,1)]⟩
 | 9284 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 108),[(32023,1)]⟩
 | 9285 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 109),[(32022,4),(32023,1)]⟩
 | 9286 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 110),[(32024,1)]⟩
 | 9287 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 111),[(32025,1)]⟩
 | 9288 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 112),[(32027,1)]⟩
 | 9289 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0044.inputs 113),[(32026,4),(32027,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B12.count
