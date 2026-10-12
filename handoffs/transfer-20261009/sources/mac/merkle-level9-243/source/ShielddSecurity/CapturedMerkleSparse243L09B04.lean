import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7026 16
def localParent : Nat → Option Row
 | 7026 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 162),[(29764,1)]⟩
 | 7027 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 163),[(29765,1)]⟩
 | 7028 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 164),[(29767,1)]⟩
 | 7029 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 165),[(29766,4),(29767,1)]⟩
 | 7030 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 166),[(29768,1)]⟩
 | 7031 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 167),[(29769,1)]⟩
 | 7032 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 168),[(29771,1)]⟩
 | 7033 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 169),[(29770,4),(29771,1)]⟩
 | 7034 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 170),[(29772,1)]⟩
 | 7035 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 171),[(29773,1)]⟩
 | 7036 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 172),[(29775,1)]⟩
 | 7037 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 173),[(29774,4),(29775,1)]⟩
 | 7038 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 174),[(29776,1)]⟩
 | 7039 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 175),[(29777,1)]⟩
 | 7040 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 176),[(29779,1)]⟩
 | 7041 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 177),[(29778,4),(29779,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B04.count
