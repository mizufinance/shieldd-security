import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0021
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4514 16
def localParent : Nat → Option Row
 | 4514 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 12),[(27252,1)]⟩
 | 4515 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 13),[(27253,1)]⟩
 | 4516 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 14),[(27255,1)]⟩
 | 4517 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 15),[(27254,4),(27255,1)]⟩
 | 4518 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 16),[(27256,1)]⟩
 | 4519 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 17),[(27257,1)]⟩
 | 4520 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 18),[(27259,1)]⟩
 | 4521 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 19),[(27258,4),(27259,1)]⟩
 | 4522 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 20),[(27260,1)]⟩
 | 4523 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 21),[(27261,1)]⟩
 | 4524 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 22),[(27263,1)]⟩
 | 4525 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 23),[(27262,4),(27263,1)]⟩
 | 4526 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 24),[(27264,1)]⟩
 | 4527 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 25),[(27265,1)]⟩
 | 4528 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 26),[(27267,1)]⟩
 | 4529 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 27),[(27266,4),(27267,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B06.count
