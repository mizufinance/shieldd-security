import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0023
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4922 16
def localParent : Nat → Option Row
 | 4922 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 58),[(27660,1)]⟩
 | 4923 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 59),[(27661,1)]⟩
 | 4924 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 60),[(27663,1)]⟩
 | 4925 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 61),[(27662,4),(27663,1)]⟩
 | 4926 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 62),[(27664,1)]⟩
 | 4927 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 63),[(27665,1)]⟩
 | 4928 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 64),[(27667,1)]⟩
 | 4929 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 65),[(27666,4),(27667,1)]⟩
 | 4930 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 66),[(27668,1)]⟩
 | 4931 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 67),[(27669,1)]⟩
 | 4932 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 68),[(27671,1)]⟩
 | 4933 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 69),[(27670,4),(27671,1)]⟩
 | 4934 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 70),[(27672,1)]⟩
 | 4935 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 71),[(27673,1)]⟩
 | 4936 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 72),[(27675,1)]⟩
 | 4937 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 73),[(27674,4),(27675,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B05.count
