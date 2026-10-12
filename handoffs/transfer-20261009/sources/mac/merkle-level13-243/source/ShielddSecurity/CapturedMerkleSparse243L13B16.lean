import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0042
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8914 16
def localParent : Nat → Option Row
 | 8914 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 124),[(31652,1)]⟩
 | 8915 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 125),[(31653,1)]⟩
 | 8916 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 126),[(31655,1)]⟩
 | 8917 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 127),[(31654,4),(31655,1)]⟩
 | 8918 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 128),[(31656,1)]⟩
 | 8919 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 129),[(31657,1)]⟩
 | 8920 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 130),[(31659,1)]⟩
 | 8921 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 131),[(31658,4),(31659,1)]⟩
 | 8922 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 132),[(31660,1)]⟩
 | 8923 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 133),[(31661,1)]⟩
 | 8924 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 134),[(31663,1)]⟩
 | 8925 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 135),[(31662,4),(31663,1)]⟩
 | 8926 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 136),[(31664,1)]⟩
 | 8927 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 137),[(31665,1)]⟩
 | 8928 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 138),[(31667,1)]⟩
 | 8929 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 139),[(31666,4),(31667,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B16.count
