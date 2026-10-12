import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6274 16
def localParent : Nat → Option Row
 | 6274 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 244),[(29012,1)]⟩
 | 6275 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 245),[(29013,1)]⟩
 | 6276 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 246),[(29015,1)]⟩
 | 6277 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 247),[(29014,4),(29015,1)]⟩
 | 6278 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 248),[(29016,1)]⟩
 | 6279 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 249),[(29017,1)]⟩
 | 6280 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 250),[(29019,1)]⟩
 | 6281 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 251),[(29018,4),(29019,1)]⟩
 | 6282 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 252),[(29020,1)]⟩
 | 6283 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 253),[(29021,1)]⟩
 | 6284 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 254),[(29023,1)]⟩
 | 6285 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 255),[(29022,4),(29023,1)]⟩
 | 6286 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 256),[(29024,1)]⟩
 | 6287 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 257),[(29025,1)]⟩
 | 6288 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 258),[(29027,1)]⟩
 | 6289 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 259),[(29026,4),(29027,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B10.count
