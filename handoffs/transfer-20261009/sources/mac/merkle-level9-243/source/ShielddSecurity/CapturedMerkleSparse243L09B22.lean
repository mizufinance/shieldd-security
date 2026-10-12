import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 300).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7314 16
def localParent : Nat → Option Row
 | 7314 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 34),[(30052,1)]⟩
 | 7315 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 35),[(30053,1)]⟩
 | 7316 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 36),[(30055,1)]⟩
 | 7317 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 37),[(30054,4),(30055,1)]⟩
 | 7318 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 38),[(30056,1)]⟩
 | 7319 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 39),[(30057,1)]⟩
 | 7320 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 40),[(30059,1)]⟩
 | 7321 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 41),[(30058,4),(30059,1)]⟩
 | 7322 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 42),[(30060,1)]⟩
 | 7323 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 43),[(30061,1)]⟩
 | 7324 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 44),[(30063,1)]⟩
 | 7325 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 45),[(30062,4),(30063,1)]⟩
 | 7326 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 46),[(30064,1)]⟩
 | 7327 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 47),[(30065,1)]⟩
 | 7328 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 48),[(30067,1)]⟩
 | 7329 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 49),[(30066,4),(30067,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B22.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B22.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B22.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B22.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B22.count
