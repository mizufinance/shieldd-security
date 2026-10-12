import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0041
import ShielddSecurity.CapturedArithmetic45B0042
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B08
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 76).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8786 16
def localParent : Nat → Option Row
 | 8786 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 258),[(31524,1)]⟩
 | 8787 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 259),[(31525,1)]⟩
 | 8788 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 260),[(31527,1)]⟩
 | 8789 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 261),[(31526,4),(31527,1)]⟩
 | 8790 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 0),[(31528,1)]⟩
 | 8791 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 1),[(31529,1)]⟩
 | 8792 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 2),[(31531,1)]⟩
 | 8793 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 3),[(31530,4),(31531,1)]⟩
 | 8794 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 4),[(31532,1)]⟩
 | 8795 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 5),[(31533,1)]⟩
 | 8796 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 6),[(31535,1)]⟩
 | 8797 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 7),[(31534,4),(31535,1)]⟩
 | 8798 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 8),[(31536,1)]⟩
 | 8799 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 9),[(31537,1)]⟩
 | 8800 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 10),[(31539,1)]⟩
 | 8801 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 11),[(31538,4),(31539,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B08

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B08.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B08.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B08.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B08.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B08.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B08.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B08.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B08.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B08.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B08.count
