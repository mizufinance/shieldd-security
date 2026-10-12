import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0034
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7170 16
def localParent : Nat → Option Row
 | 7170 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 0),[(29908,1)]⟩
 | 7171 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 1),[(29909,1)]⟩
 | 7172 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 2),[(29911,1)]⟩
 | 7173 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 3),[(29910,4),(29911,1)]⟩
 | 7174 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 4),[(29912,1)]⟩
 | 7175 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 5),[(29913,1)]⟩
 | 7176 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 6),[(29915,1)]⟩
 | 7177 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 7),[(29914,4),(29915,1)]⟩
 | 7178 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 8),[(29916,1)]⟩
 | 7179 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 9),[(29917,1)]⟩
 | 7180 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 10),[(29919,1)]⟩
 | 7181 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 11),[(29918,4),(29919,1)]⟩
 | 7182 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 12),[(29920,1)]⟩
 | 7183 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 13),[(29921,1)]⟩
 | 7184 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 14),[(29923,1)]⟩
 | 7185 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 15),[(29922,4),(29923,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B13.count
