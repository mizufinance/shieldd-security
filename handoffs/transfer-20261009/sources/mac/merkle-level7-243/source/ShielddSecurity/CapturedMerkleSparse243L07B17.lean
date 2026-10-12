import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0030
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6386 16
def localParent : Nat → Option Row
 | 6386 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 38),[(29124,1)]⟩
 | 6387 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 39),[(29125,1)]⟩
 | 6388 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 40),[(29127,1)]⟩
 | 6389 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 41),[(29126,4),(29127,1)]⟩
 | 6390 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 42),[(29128,1)]⟩
 | 6391 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 43),[(29129,1)]⟩
 | 6392 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 44),[(29131,1)]⟩
 | 6393 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 45),[(29130,4),(29131,1)]⟩
 | 6394 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 46),[(29132,1)]⟩
 | 6395 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 47),[(29133,1)]⟩
 | 6396 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 48),[(29135,1)]⟩
 | 6397 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 49),[(29134,4),(29135,1)]⟩
 | 6398 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 50),[(29136,1)]⟩
 | 6399 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 51),[(29137,1)]⟩
 | 6400 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 52),[(29139,1)]⟩
 | 6401 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 53),[(29138,4),(29139,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B17.count
