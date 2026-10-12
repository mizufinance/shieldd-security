import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0030
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6370 16
def localParent : Nat → Option Row
 | 6370 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 22),[(29108,1)]⟩
 | 6371 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 23),[(29109,1)]⟩
 | 6372 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 24),[(29111,1)]⟩
 | 6373 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 25),[(29110,4),(29111,1)]⟩
 | 6374 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 26),[(29112,1)]⟩
 | 6375 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 27),[(29113,1)]⟩
 | 6376 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 28),[(29115,1)]⟩
 | 6377 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 29),[(29114,4),(29115,1)]⟩
 | 6378 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 30),[(29116,1)]⟩
 | 6379 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 31),[(29117,1)]⟩
 | 6380 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 32),[(29119,1)]⟩
 | 6381 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 33),[(29118,4),(29119,1)]⟩
 | 6382 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 34),[(29120,1)]⟩
 | 6383 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 35),[(29121,1)]⟩
 | 6384 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 36),[(29123,1)]⟩
 | 6385 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 37),[(29122,4),(29123,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B16.count
