import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6322 16
def localParent : Nat → Option Row
 | 6322 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 292),[(29060,1)]⟩
 | 6323 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 293),[(29061,1)]⟩
 | 6324 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 294),[(29063,1)]⟩
 | 6325 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 295),[(29062,4),(29063,1)]⟩
 | 6326 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 296),[(29064,1)]⟩
 | 6327 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 297),[(29065,1)]⟩
 | 6328 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 298),[(29067,1)]⟩
 | 6329 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 299),[(29066,4),(29067,1)]⟩
 | 6330 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 300),[(29068,1)]⟩
 | 6331 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 301),[(29069,1)]⟩
 | 6332 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 302),[(29071,1)]⟩
 | 6333 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 303),[(29070,4),(29071,1)]⟩
 | 6334 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 304),[(29072,1)]⟩
 | 6335 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 305),[(29073,1)]⟩
 | 6336 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 306),[(29075,1)]⟩
 | 6337 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 307),[(29074,4),(29075,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B13.count
