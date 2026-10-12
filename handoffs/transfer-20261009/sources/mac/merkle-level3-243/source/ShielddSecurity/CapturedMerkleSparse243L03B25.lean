import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0022
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4818 16
def localParent : Nat → Option Row
 | 4818 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 124),[(27556,1)]⟩
 | 4819 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 125),[(27557,1)]⟩
 | 4820 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 126),[(27559,1)]⟩
 | 4821 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 127),[(27558,4),(27559,1)]⟩
 | 4822 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 128),[(27560,1)]⟩
 | 4823 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 129),[(27561,1)]⟩
 | 4824 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 130),[(27563,1)]⟩
 | 4825 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 131),[(27562,4),(27563,1)]⟩
 | 4826 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 132),[(27564,1)]⟩
 | 4827 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 133),[(27565,1)]⟩
 | 4828 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 134),[(27567,1)]⟩
 | 4829 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 135),[(27566,4),(27567,1)]⟩
 | 4830 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 136),[(27568,1)]⟩
 | 4831 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 137),[(27569,1)]⟩
 | 4832 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 138),[(27571,1)]⟩
 | 4833 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 139),[(27570,4),(27571,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B25.count
