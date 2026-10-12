import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0043
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8962 16
def localParent : Nat → Option Row
 | 8962 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 18),[(31700,1)]⟩
 | 8963 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 19),[(31701,1)]⟩
 | 8964 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 20),[(31703,1)]⟩
 | 8965 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 21),[(31702,4),(31703,1)]⟩
 | 8966 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 22),[(31704,1)]⟩
 | 8967 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 23),[(31705,1)]⟩
 | 8968 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 24),[(31707,1)]⟩
 | 8969 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 25),[(31706,4),(31707,1)]⟩
 | 8970 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 26),[(31708,1)]⟩
 | 8971 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 27),[(31709,1)]⟩
 | 8972 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 28),[(31711,1)]⟩
 | 8973 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 29),[(31710,4),(31711,1)]⟩
 | 8974 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 30),[(31712,1)]⟩
 | 8975 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 31),[(31713,1)]⟩
 | 8976 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 32),[(31715,1)]⟩
 | 8977 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 33),[(31714,4),(31715,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B19.count
