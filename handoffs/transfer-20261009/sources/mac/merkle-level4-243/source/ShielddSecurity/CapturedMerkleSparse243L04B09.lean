import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0023
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L04B09
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 92).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2544)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4986 16
def localParent : Nat → Option Row
 | 4986 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 122),[(27724,1)]⟩
 | 4987 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 123),[(27725,1)]⟩
 | 4988 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 124),[(27727,1)]⟩
 | 4989 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 125),[(27726,4),(27727,1)]⟩
 | 4990 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 126),[(27728,1)]⟩
 | 4991 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 127),[(27729,1)]⟩
 | 4992 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 128),[(27731,1)]⟩
 | 4993 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 129),[(27730,4),(27731,1)]⟩
 | 4994 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 130),[(27732,1)]⟩
 | 4995 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 131),[(27733,1)]⟩
 | 4996 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 132),[(27735,1)]⟩
 | 4997 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 133),[(27734,4),(27735,1)]⟩
 | 4998 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 134),[(27736,1)]⟩
 | 4999 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 135),[(27737,1)]⟩
 | 5000 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 136),[(27739,1)]⟩
 | 5001 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0023.inputs 137),[(27738,4),(27739,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L04B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B09.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B09.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B09.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B09.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B09.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B09.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B09.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L04B09.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L04B09.count
