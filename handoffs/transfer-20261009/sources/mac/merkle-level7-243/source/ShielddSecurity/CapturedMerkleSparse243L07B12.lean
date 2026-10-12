import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6306 16
def localParent : Nat → Option Row
 | 6306 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 276),[(29044,1)]⟩
 | 6307 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 277),[(29045,1)]⟩
 | 6308 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 278),[(29047,1)]⟩
 | 6309 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 279),[(29046,4),(29047,1)]⟩
 | 6310 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 280),[(29048,1)]⟩
 | 6311 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 281),[(29049,1)]⟩
 | 6312 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 282),[(29051,1)]⟩
 | 6313 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 283),[(29050,4),(29051,1)]⟩
 | 6314 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 284),[(29052,1)]⟩
 | 6315 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 285),[(29053,1)]⟩
 | 6316 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 286),[(29055,1)]⟩
 | 6317 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 287),[(29054,4),(29055,1)]⟩
 | 6318 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 288),[(29056,1)]⟩
 | 6319 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 289),[(29057,1)]⟩
 | 6320 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 290),[(29059,1)]⟩
 | 6321 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 291),[(29058,4),(29059,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B12.count
