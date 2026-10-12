import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0042
import ShielddSecurity.CapturedArithmetic45B0043
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8930 16
def localParent : Nat → Option Row
 | 8930 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 140),[(31668,1)]⟩
 | 8931 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 141),[(31669,1)]⟩
 | 8932 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 142),[(31671,1)]⟩
 | 8933 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 143),[(31670,4),(31671,1)]⟩
 | 8934 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 144),[(31672,1)]⟩
 | 8935 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 145),[(31673,1)]⟩
 | 8936 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 146),[(31675,1)]⟩
 | 8937 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 147),[(31674,4),(31675,1)]⟩
 | 8938 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 148),[(31676,1)]⟩
 | 8939 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 149),[(31677,1)]⟩
 | 8940 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 150),[(31679,1)]⟩
 | 8941 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 151),[(31678,4),(31679,1)]⟩
 | 8942 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 152),[(31680,1)]⟩
 | 8943 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0042.inputs 153),[(31681,1)]⟩
 | 8944 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 0),[(31683,1)]⟩
 | 8945 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 1),[(31682,4),(31683,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B17.count
