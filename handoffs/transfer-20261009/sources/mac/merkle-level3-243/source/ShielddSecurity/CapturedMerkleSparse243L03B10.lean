import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0021
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4578 16
def localParent : Nat → Option Row
 | 4578 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 76),[(27316,1)]⟩
 | 4579 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 77),[(27317,1)]⟩
 | 4580 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 78),[(27319,1)]⟩
 | 4581 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 79),[(27318,4),(27319,1)]⟩
 | 4582 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 80),[(27320,1)]⟩
 | 4583 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 81),[(27321,1)]⟩
 | 4584 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 82),[(27323,1)]⟩
 | 4585 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 83),[(27322,4),(27323,1)]⟩
 | 4586 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 84),[(27324,1)]⟩
 | 4587 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 85),[(27325,1)]⟩
 | 4588 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 86),[(27327,1)]⟩
 | 4589 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 87),[(27326,4),(27327,1)]⟩
 | 4590 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 88),[(27328,1)]⟩
 | 4591 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 89),[(27329,1)]⟩
 | 4592 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 90),[(27331,1)]⟩
 | 4593 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 91),[(27330,4),(27331,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B10.count
