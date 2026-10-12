import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0034
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7250 16
def localParent : Nat → Option Row
 | 7250 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 80),[(29988,1)]⟩
 | 7251 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 81),[(29989,1)]⟩
 | 7252 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 82),[(29991,1)]⟩
 | 7253 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 83),[(29990,4),(29991,1)]⟩
 | 7254 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 84),[(29992,1)]⟩
 | 7255 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 85),[(29993,1)]⟩
 | 7256 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 86),[(29995,1)]⟩
 | 7257 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 87),[(29994,4),(29995,1)]⟩
 | 7258 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 88),[(29996,1)]⟩
 | 7259 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 89),[(29997,1)]⟩
 | 7260 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 90),[(29999,1)]⟩
 | 7261 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 91),[(29998,4),(29999,1)]⟩
 | 7262 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 92),[(30000,1)]⟩
 | 7263 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 93),[(30001,1)]⟩
 | 7264 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 94),[(30003,1)]⟩
 | 7265 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 95),[(30002,4),(30003,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B18.count
