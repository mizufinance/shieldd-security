import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0034
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7266 16
def localParent : Nat → Option Row
 | 7266 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 96),[(30004,1)]⟩
 | 7267 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 97),[(30005,1)]⟩
 | 7268 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 98),[(30007,1)]⟩
 | 7269 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 99),[(30006,4),(30007,1)]⟩
 | 7270 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 100),[(30008,1)]⟩
 | 7271 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 101),[(30009,1)]⟩
 | 7272 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 102),[(30011,1)]⟩
 | 7273 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 103),[(30010,4),(30011,1)]⟩
 | 7274 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 104),[(30012,1)]⟩
 | 7275 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 105),[(30013,1)]⟩
 | 7276 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 106),[(30015,1)]⟩
 | 7277 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 107),[(30014,4),(30015,1)]⟩
 | 7278 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 108),[(30016,1)]⟩
 | 7279 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 109),[(30017,1)]⟩
 | 7280 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 0),[(30019,1)]⟩
 | 7281 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 1),[(30018,4),(30019,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B19.count
