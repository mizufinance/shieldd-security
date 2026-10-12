import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0043
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8978 16
def localParent : Nat → Option Row
 | 8978 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 34),[(31716,1)]⟩
 | 8979 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 35),[(31717,1)]⟩
 | 8980 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 36),[(31719,1)]⟩
 | 8981 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 37),[(31718,4),(31719,1)]⟩
 | 8982 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 38),[(31720,1)]⟩
 | 8983 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 39),[(31721,1)]⟩
 | 8984 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 40),[(31723,1)]⟩
 | 8985 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 41),[(31722,4),(31723,1)]⟩
 | 8986 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 42),[(31724,1)]⟩
 | 8987 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 43),[(31725,1)]⟩
 | 8988 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 44),[(31727,1)]⟩
 | 8989 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 45),[(31726,4),(31727,1)]⟩
 | 8990 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 46),[(31728,1)]⟩
 | 8991 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 47),[(31729,1)]⟩
 | 8992 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 48),[(31731,1)]⟩
 | 8993 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 49),[(31730,4),(31731,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B20.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B20.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B20.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B20.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B20.count
