import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0045
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9402 16
def localParent : Nat → Option Row
 | 9402 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 42),[(32140,1)]⟩
 | 9403 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 43),[(32141,1)]⟩
 | 9404 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 44),[(32143,1)]⟩
 | 9405 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 45),[(32142,4),(32143,1)]⟩
 | 9406 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 46),[(32144,1)]⟩
 | 9407 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 47),[(32145,1)]⟩
 | 9408 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 48),[(32147,1)]⟩
 | 9409 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 49),[(32146,4),(32147,1)]⟩
 | 9410 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 50),[(32148,1)]⟩
 | 9411 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 51),[(32149,1)]⟩
 | 9412 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 52),[(32151,1)]⟩
 | 9413 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 53),[(32150,4),(32151,1)]⟩
 | 9414 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 54),[(32152,1)]⟩
 | 9415 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 55),[(32153,1)]⟩
 | 9416 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 56),[(32155,1)]⟩
 | 9417 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 57),[(32154,4),(32155,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B20.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B20.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B20.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B20.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B20.count
