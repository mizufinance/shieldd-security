import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0021
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B08
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 76).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4546 16
def localParent : Nat → Option Row
 | 4546 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 44),[(27284,1)]⟩
 | 4547 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 45),[(27285,1)]⟩
 | 4548 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 46),[(27287,1)]⟩
 | 4549 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 47),[(27286,4),(27287,1)]⟩
 | 4550 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 48),[(27288,1)]⟩
 | 4551 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 49),[(27289,1)]⟩
 | 4552 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 50),[(27291,1)]⟩
 | 4553 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 51),[(27290,4),(27291,1)]⟩
 | 4554 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 52),[(27292,1)]⟩
 | 4555 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 53),[(27293,1)]⟩
 | 4556 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 54),[(27295,1)]⟩
 | 4557 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 55),[(27294,4),(27295,1)]⟩
 | 4558 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 56),[(27296,1)]⟩
 | 4559 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 57),[(27297,1)]⟩
 | 4560 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 58),[(27299,1)]⟩
 | 4561 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 59),[(27298,4),(27299,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B08

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B08.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B08.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B08.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B08.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B08.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B08.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B08.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B08.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B08.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B08.count
