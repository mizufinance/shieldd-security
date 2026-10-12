import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0043
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8994 16
def localParent : Nat → Option Row
 | 8994 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 50),[(31732,1)]⟩
 | 8995 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 51),[(31733,1)]⟩
 | 8996 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 52),[(31735,1)]⟩
 | 8997 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 53),[(31734,4),(31735,1)]⟩
 | 8998 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 54),[(31736,1)]⟩
 | 8999 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 55),[(31737,1)]⟩
 | 9000 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 56),[(31739,1)]⟩
 | 9001 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 57),[(31738,4),(31739,1)]⟩
 | 9002 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 58),[(31740,1)]⟩
 | 9003 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 59),[(31741,1)]⟩
 | 9004 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 60),[(31743,1)]⟩
 | 9005 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 61),[(31742,4),(31743,1)]⟩
 | 9006 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 62),[(31744,1)]⟩
 | 9007 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 63),[(31745,1)]⟩
 | 9008 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 64),[(31747,1)]⟩
 | 9009 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 65),[(31746,4),(31747,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B21.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B21.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B21.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B21.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B21.count
