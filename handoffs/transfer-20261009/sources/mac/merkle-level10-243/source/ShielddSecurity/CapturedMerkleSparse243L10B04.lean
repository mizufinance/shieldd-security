import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7450 16
def localParent : Nat → Option Row
 | 7450 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 170),[(30188,1)]⟩
 | 7451 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 171),[(30189,1)]⟩
 | 7452 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 172),[(30191,1)]⟩
 | 7453 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 173),[(30190,4),(30191,1)]⟩
 | 7454 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 174),[(30192,1)]⟩
 | 7455 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 175),[(30193,1)]⟩
 | 7456 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 176),[(30195,1)]⟩
 | 7457 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 177),[(30194,4),(30195,1)]⟩
 | 7458 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 178),[(30196,1)]⟩
 | 7459 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 179),[(30197,1)]⟩
 | 7460 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 180),[(30199,1)]⟩
 | 7461 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 181),[(30198,4),(30199,1)]⟩
 | 7462 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 182),[(30200,1)]⟩
 | 7463 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 183),[(30201,1)]⟩
 | 7464 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 184),[(30203,1)]⟩
 | 7465 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 185),[(30202,4),(30203,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B04.count
