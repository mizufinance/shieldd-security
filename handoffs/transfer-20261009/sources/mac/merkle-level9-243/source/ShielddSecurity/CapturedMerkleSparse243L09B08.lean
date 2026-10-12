import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B08
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 76).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7090 16
def localParent : Nat → Option Row
 | 7090 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 226),[(29828,1)]⟩
 | 7091 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 227),[(29829,1)]⟩
 | 7092 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 228),[(29831,1)]⟩
 | 7093 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 229),[(29830,4),(29831,1)]⟩
 | 7094 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 230),[(29832,1)]⟩
 | 7095 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 231),[(29833,1)]⟩
 | 7096 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 232),[(29835,1)]⟩
 | 7097 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 233),[(29834,4),(29835,1)]⟩
 | 7098 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 234),[(29836,1)]⟩
 | 7099 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 235),[(29837,1)]⟩
 | 7100 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 236),[(29839,1)]⟩
 | 7101 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 237),[(29838,4),(29839,1)]⟩
 | 7102 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 238),[(29840,1)]⟩
 | 7103 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 239),[(29841,1)]⟩
 | 7104 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 240),[(29843,1)]⟩
 | 7105 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 241),[(29842,4),(29843,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B08

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B08.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B08.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B08.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B08.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B08.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B08.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B08.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B08.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B08.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B08.count
