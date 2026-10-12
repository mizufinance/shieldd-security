import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0022
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 316).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4786 16
def localParent : Nat → Option Row
 | 4786 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 92),[(27524,1)]⟩
 | 4787 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 93),[(27525,1)]⟩
 | 4788 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 94),[(27527,1)]⟩
 | 4789 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 95),[(27526,4),(27527,1)]⟩
 | 4790 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 96),[(27528,1)]⟩
 | 4791 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 97),[(27529,1)]⟩
 | 4792 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 98),[(27531,1)]⟩
 | 4793 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 99),[(27530,4),(27531,1)]⟩
 | 4794 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 100),[(27532,1)]⟩
 | 4795 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 101),[(27533,1)]⟩
 | 4796 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 102),[(27535,1)]⟩
 | 4797 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 103),[(27534,4),(27535,1)]⟩
 | 4798 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 104),[(27536,1)]⟩
 | 4799 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 105),[(27537,1)]⟩
 | 4800 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 106),[(27539,1)]⟩
 | 4801 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 107),[(27538,4),(27539,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B23.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B23.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B23.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B23.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B23.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B23.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B23.count
