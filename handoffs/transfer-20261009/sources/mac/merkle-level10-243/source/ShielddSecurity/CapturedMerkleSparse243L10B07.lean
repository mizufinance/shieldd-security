import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0035
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L10B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5088)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7498 16
def localParent : Nat → Option Row
 | 7498 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 218),[(30236,1)]⟩
 | 7499 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 219),[(30237,1)]⟩
 | 7500 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 220),[(30239,1)]⟩
 | 7501 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 221),[(30238,4),(30239,1)]⟩
 | 7502 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 222),[(30240,1)]⟩
 | 7503 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 223),[(30241,1)]⟩
 | 7504 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 224),[(30243,1)]⟩
 | 7505 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 225),[(30242,4),(30243,1)]⟩
 | 7506 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 226),[(30244,1)]⟩
 | 7507 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 227),[(30245,1)]⟩
 | 7508 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 228),[(30247,1)]⟩
 | 7509 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 229),[(30246,4),(30247,1)]⟩
 | 7510 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 230),[(30248,1)]⟩
 | 7511 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 231),[(30249,1)]⟩
 | 7512 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 232),[(30251,1)]⟩
 | 7513 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0035.inputs 233),[(30250,4),(30251,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L10B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L10B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L10B07.count
