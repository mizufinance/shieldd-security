import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7466 16
def localParent : Nat → Option Row
 | 7466 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 186),[(30204,1)]⟩
 | 7467 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 187),[(30205,1)]⟩
 | 7468 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 188),[(30207,1)]⟩
 | 7469 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 189),[(30206,4),(30207,1)]⟩
 | 7470 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 190),[(30208,1)]⟩
 | 7471 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 191),[(30209,1)]⟩
 | 7472 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 192),[(30211,1)]⟩
 | 7473 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 193),[(30210,4),(30211,1)]⟩
 | 7474 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 194),[(30212,1)]⟩
 | 7475 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 195),[(30213,1)]⟩
 | 7476 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 196),[(30215,1)]⟩
 | 7477 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 197),[(30214,4),(30215,1)]⟩
 | 7478 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 198),[(30216,1)]⟩
 | 7479 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 199),[(30217,1)]⟩
 | 7480 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 200),[(30219,1)]⟩
 | 7481 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 201),[(30218,4),(30219,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B05.count
