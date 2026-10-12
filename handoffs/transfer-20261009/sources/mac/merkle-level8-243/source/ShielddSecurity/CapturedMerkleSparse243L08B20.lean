import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0032
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6858 16
def localParent : Nat → Option Row
 | 6858 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 98),[(29596,1)]⟩
 | 6859 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 99),[(29597,1)]⟩
 | 6860 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 100),[(29599,1)]⟩
 | 6861 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 101),[(29598,4),(29599,1)]⟩
 | 6862 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 102),[(29600,1)]⟩
 | 6863 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 103),[(29601,1)]⟩
 | 6864 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 0),[(29603,1)]⟩
 | 6865 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 1),[(29602,4),(29603,1)]⟩
 | 6866 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 2),[(29604,1)]⟩
 | 6867 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 3),[(29605,1)]⟩
 | 6868 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 4),[(29607,1)]⟩
 | 6869 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 5),[(29606,4),(29607,1)]⟩
 | 6870 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 6),[(29608,1)]⟩
 | 6871 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 7),[(29609,1)]⟩
 | 6872 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 8),[(29611,1)]⟩
 | 6873 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 9),[(29610,4),(29611,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B20.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B20.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B20.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B20.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B20.count
