import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0022
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4722 16
def localParent : Nat → Option Row
 | 4722 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 28),[(27460,1)]⟩
 | 4723 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 29),[(27461,1)]⟩
 | 4724 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 30),[(27463,1)]⟩
 | 4725 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 31),[(27462,4),(27463,1)]⟩
 | 4726 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 32),[(27464,1)]⟩
 | 4727 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 33),[(27465,1)]⟩
 | 4728 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 34),[(27467,1)]⟩
 | 4729 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 35),[(27466,4),(27467,1)]⟩
 | 4730 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 36),[(27468,1)]⟩
 | 4731 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 37),[(27469,1)]⟩
 | 4732 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 38),[(27471,1)]⟩
 | 4733 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 39),[(27470,4),(27471,1)]⟩
 | 4734 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 40),[(27472,1)]⟩
 | 4735 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 41),[(27473,1)]⟩
 | 4736 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 42),[(27475,1)]⟩
 | 4737 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 43),[(27474,4),(27475,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B19.count
