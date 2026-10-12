import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0041
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8770 16
def localParent : Nat → Option Row
 | 8770 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 242),[(31508,1)]⟩
 | 8771 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 243),[(31509,1)]⟩
 | 8772 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 244),[(31511,1)]⟩
 | 8773 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 245),[(31510,4),(31511,1)]⟩
 | 8774 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 246),[(31512,1)]⟩
 | 8775 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 247),[(31513,1)]⟩
 | 8776 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 248),[(31515,1)]⟩
 | 8777 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 249),[(31514,4),(31515,1)]⟩
 | 8778 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 250),[(31516,1)]⟩
 | 8779 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 251),[(31517,1)]⟩
 | 8780 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 252),[(31519,1)]⟩
 | 8781 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 253),[(31518,4),(31519,1)]⟩
 | 8782 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 254),[(31520,1)]⟩
 | 8783 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 255),[(31521,1)]⟩
 | 8784 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 256),[(31523,1)]⟩
 | 8785 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 257),[(31522,4),(31523,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B07.count
