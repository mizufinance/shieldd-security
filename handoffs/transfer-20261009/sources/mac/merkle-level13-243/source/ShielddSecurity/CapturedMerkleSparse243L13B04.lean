import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0041
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8722 16
def localParent : Nat → Option Row
 | 8722 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 194),[(31460,1)]⟩
 | 8723 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 195),[(31461,1)]⟩
 | 8724 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 196),[(31463,1)]⟩
 | 8725 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 197),[(31462,4),(31463,1)]⟩
 | 8726 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 198),[(31464,1)]⟩
 | 8727 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 199),[(31465,1)]⟩
 | 8728 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 200),[(31467,1)]⟩
 | 8729 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 201),[(31466,4),(31467,1)]⟩
 | 8730 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 202),[(31468,1)]⟩
 | 8731 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 203),[(31469,1)]⟩
 | 8732 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 204),[(31471,1)]⟩
 | 8733 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 205),[(31470,4),(31471,1)]⟩
 | 8734 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 206),[(31472,1)]⟩
 | 8735 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 207),[(31473,1)]⟩
 | 8736 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 208),[(31475,1)]⟩
 | 8737 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 209),[(31474,4),(31475,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B04.count
