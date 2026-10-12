import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0022
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4738 16
def localParent : Nat → Option Row
 | 4738 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 44),[(27476,1)]⟩
 | 4739 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 45),[(27477,1)]⟩
 | 4740 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 46),[(27479,1)]⟩
 | 4741 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 47),[(27478,4),(27479,1)]⟩
 | 4742 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 48),[(27480,1)]⟩
 | 4743 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 49),[(27481,1)]⟩
 | 4744 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 50),[(27483,1)]⟩
 | 4745 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 51),[(27482,4),(27483,1)]⟩
 | 4746 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 52),[(27484,1)]⟩
 | 4747 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 53),[(27485,1)]⟩
 | 4748 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 54),[(27487,1)]⟩
 | 4749 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 55),[(27486,4),(27487,1)]⟩
 | 4750 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 56),[(27488,1)]⟩
 | 4751 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 57),[(27489,1)]⟩
 | 4752 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 58),[(27491,1)]⟩
 | 4753 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 59),[(27490,4),(27491,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B20.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B20.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B20.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B20.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B20.count
