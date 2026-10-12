import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CapturedArithmetic45B0030
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B14
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 172).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6338 16
def localParent : Nat → Option Row
 | 6338 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 308),[(29076,1)]⟩
 | 6339 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 309),[(29077,1)]⟩
 | 6340 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 310),[(29079,1)]⟩
 | 6341 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 311),[(29078,4),(29079,1)]⟩
 | 6342 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 312),[(29080,1)]⟩
 | 6343 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 313),[(29081,1)]⟩
 | 6344 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 314),[(29083,1)]⟩
 | 6345 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 315),[(29082,4),(29083,1)]⟩
 | 6346 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 316),[(29084,1)]⟩
 | 6347 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 317),[(29085,1)]⟩
 | 6348 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 0),[(29087,1)]⟩
 | 6349 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 1),[(29086,4),(29087,1)]⟩
 | 6350 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 2),[(29088,1)]⟩
 | 6351 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 3),[(29089,1)]⟩
 | 6352 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 4),[(29091,1)]⟩
 | 6353 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 5),[(29090,4),(29091,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B14

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B14.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B14.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B14.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B14.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B14.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B14.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B14.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B14.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B14.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B14.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B14.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B14.count
