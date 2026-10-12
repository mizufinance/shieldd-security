import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0017
import ShielddSecurity.CapturedArithmetic45B0018
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3858 16
def localParent : Nat → Option Row
 | 3858 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 134),[(26596,1)]⟩
 | 3859 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 135),[(26597,1)]⟩
 | 3860 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 136),[(26599,1)]⟩
 | 3861 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 137),[(26598,4),(26599,1)]⟩
 | 3862 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 0),[(26600,1)]⟩
 | 3863 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 1),[(26601,1)]⟩
 | 3864 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 2),[(26603,1)]⟩
 | 3865 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 3),[(26602,4),(26603,1)]⟩
 | 3866 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 4),[(26604,1)]⟩
 | 3867 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 5),[(26605,1)]⟩
 | 3868 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 6),[(26607,1)]⟩
 | 3869 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 7),[(26606,4),(26607,1)]⟩
 | 3870 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 8),[(26608,1)]⟩
 | 3871 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 9),[(26609,1)]⟩
 | 3872 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 10),[(26611,1)]⟩
 | 3873 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0018.inputs 11),[(26610,4),(26611,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B18.count
