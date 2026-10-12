import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0041
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8554 16
def localParent : Nat → Option Row
 | 8554 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 26),[(31292,1)]⟩
 | 8555 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 27),[(31293,1)]⟩
 | 8556 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 28),[(31295,1)]⟩
 | 8557 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 29),[(31294,4),(31295,1)]⟩
 | 8558 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 30),[(31296,1)]⟩
 | 8559 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 31),[(31297,1)]⟩
 | 8560 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 32),[(31299,1)]⟩
 | 8561 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 33),[(31298,4),(31299,1)]⟩
 | 8562 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 34),[(31300,1)]⟩
 | 8563 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 35),[(31301,1)]⟩
 | 8564 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 36),[(31303,1)]⟩
 | 8565 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 37),[(31302,4),(31303,1)]⟩
 | 8566 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 38),[(31304,1)]⟩
 | 8567 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 39),[(31305,1)]⟩
 | 8568 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 40),[(31307,1)]⟩
 | 8569 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 41),[(31306,4),(31307,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B20.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B20.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B20.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B20.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B20.count
