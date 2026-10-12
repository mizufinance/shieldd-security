import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0032
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6810 16
def localParent : Nat → Option Row
 | 6810 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 50),[(29548,1)]⟩
 | 6811 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 51),[(29549,1)]⟩
 | 6812 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 52),[(29551,1)]⟩
 | 6813 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 53),[(29550,4),(29551,1)]⟩
 | 6814 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 54),[(29552,1)]⟩
 | 6815 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 55),[(29553,1)]⟩
 | 6816 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 56),[(29555,1)]⟩
 | 6817 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 57),[(29554,4),(29555,1)]⟩
 | 6818 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 58),[(29556,1)]⟩
 | 6819 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 59),[(29557,1)]⟩
 | 6820 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 60),[(29559,1)]⟩
 | 6821 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 61),[(29558,4),(29559,1)]⟩
 | 6822 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 62),[(29560,1)]⟩
 | 6823 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 63),[(29561,1)]⟩
 | 6824 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 64),[(29563,1)]⟩
 | 6825 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 65),[(29562,4),(29563,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B17.count
