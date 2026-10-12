import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0022
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4754 16
def localParent : Nat → Option Row
 | 4754 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 60),[(27492,1)]⟩
 | 4755 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 61),[(27493,1)]⟩
 | 4756 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 62),[(27495,1)]⟩
 | 4757 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 63),[(27494,4),(27495,1)]⟩
 | 4758 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 64),[(27496,1)]⟩
 | 4759 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 65),[(27497,1)]⟩
 | 4760 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 66),[(27499,1)]⟩
 | 4761 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 67),[(27498,4),(27499,1)]⟩
 | 4762 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 68),[(27500,1)]⟩
 | 4763 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 69),[(27501,1)]⟩
 | 4764 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 70),[(27503,1)]⟩
 | 4765 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 71),[(27502,4),(27503,1)]⟩
 | 4766 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 72),[(27504,1)]⟩
 | 4767 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 73),[(27505,1)]⟩
 | 4768 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 74),[(27507,1)]⟩
 | 4769 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 75),[(27506,4),(27507,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B21.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B21.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B21.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B21.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B21.count
