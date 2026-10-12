import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0032
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B14
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 172).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6762 16
def localParent : Nat → Option Row
 | 6762 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 2),[(29500,1)]⟩
 | 6763 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 3),[(29501,1)]⟩
 | 6764 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 4),[(29503,1)]⟩
 | 6765 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 5),[(29502,4),(29503,1)]⟩
 | 6766 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 6),[(29504,1)]⟩
 | 6767 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 7),[(29505,1)]⟩
 | 6768 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 8),[(29507,1)]⟩
 | 6769 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 9),[(29506,4),(29507,1)]⟩
 | 6770 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 10),[(29508,1)]⟩
 | 6771 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 11),[(29509,1)]⟩
 | 6772 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 12),[(29511,1)]⟩
 | 6773 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 13),[(29510,4),(29511,1)]⟩
 | 6774 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 14),[(29512,1)]⟩
 | 6775 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 15),[(29513,1)]⟩
 | 6776 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 16),[(29515,1)]⟩
 | 6777 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 17),[(29514,4),(29515,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B14

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B14.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B14.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B14.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B14.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B14.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B14.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B14.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B14.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B14.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B14.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B14.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B14.count
