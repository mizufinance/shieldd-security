import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0022
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 300).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4770 16
def localParent : Nat → Option Row
 | 4770 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 76),[(27508,1)]⟩
 | 4771 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 77),[(27509,1)]⟩
 | 4772 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 78),[(27511,1)]⟩
 | 4773 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 79),[(27510,4),(27511,1)]⟩
 | 4774 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 80),[(27512,1)]⟩
 | 4775 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 81),[(27513,1)]⟩
 | 4776 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 82),[(27515,1)]⟩
 | 4777 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 83),[(27514,4),(27515,1)]⟩
 | 4778 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 84),[(27516,1)]⟩
 | 4779 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 85),[(27517,1)]⟩
 | 4780 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 86),[(27519,1)]⟩
 | 4781 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 87),[(27518,4),(27519,1)]⟩
 | 4782 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 88),[(27520,1)]⟩
 | 4783 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 89),[(27521,1)]⟩
 | 4784 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 90),[(27523,1)]⟩
 | 4785 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 91),[(27522,4),(27523,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B22.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B22.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B22.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B22.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B22.count
