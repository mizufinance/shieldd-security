import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0037
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7722 16
def localParent : Nat → Option Row
 | 7722 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 26),[(30460,1)]⟩
 | 7723 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 27),[(30461,1)]⟩
 | 7724 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 28),[(30463,1)]⟩
 | 7725 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 29),[(30462,4),(30463,1)]⟩
 | 7726 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 30),[(30464,1)]⟩
 | 7727 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 31),[(30465,1)]⟩
 | 7728 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 32),[(30467,1)]⟩
 | 7729 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 33),[(30466,4),(30467,1)]⟩
 | 7730 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 34),[(30468,1)]⟩
 | 7731 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 35),[(30469,1)]⟩
 | 7732 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 36),[(30471,1)]⟩
 | 7733 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 37),[(30470,4),(30471,1)]⟩
 | 7734 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 38),[(30472,1)]⟩
 | 7735 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 39),[(30473,1)]⟩
 | 7736 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 40),[(30475,1)]⟩
 | 7737 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0037.inputs 41),[(30474,4),(30475,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B21.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B21.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B21.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B21.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B21.count
