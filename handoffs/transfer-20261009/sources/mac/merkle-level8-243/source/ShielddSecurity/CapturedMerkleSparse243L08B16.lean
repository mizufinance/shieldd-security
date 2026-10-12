import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0032
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6794 16
def localParent : Nat → Option Row
 | 6794 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 34),[(29532,1)]⟩
 | 6795 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 35),[(29533,1)]⟩
 | 6796 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 36),[(29535,1)]⟩
 | 6797 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 37),[(29534,4),(29535,1)]⟩
 | 6798 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 38),[(29536,1)]⟩
 | 6799 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 39),[(29537,1)]⟩
 | 6800 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 40),[(29539,1)]⟩
 | 6801 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 41),[(29538,4),(29539,1)]⟩
 | 6802 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 42),[(29540,1)]⟩
 | 6803 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 43),[(29541,1)]⟩
 | 6804 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 44),[(29543,1)]⟩
 | 6805 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 45),[(29542,4),(29543,1)]⟩
 | 6806 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 46),[(29544,1)]⟩
 | 6807 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 47),[(29545,1)]⟩
 | 6808 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 48),[(29547,1)]⟩
 | 6809 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 49),[(29546,4),(29547,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B16.count
