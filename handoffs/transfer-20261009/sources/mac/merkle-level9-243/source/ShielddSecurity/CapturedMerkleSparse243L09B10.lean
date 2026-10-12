import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7122 16
def localParent : Nat → Option Row
 | 7122 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 258),[(29860,1)]⟩
 | 7123 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 259),[(29861,1)]⟩
 | 7124 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 260),[(29863,1)]⟩
 | 7125 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 261),[(29862,4),(29863,1)]⟩
 | 7126 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 262),[(29864,1)]⟩
 | 7127 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 263),[(29865,1)]⟩
 | 7128 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 264),[(29867,1)]⟩
 | 7129 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 265),[(29866,4),(29867,1)]⟩
 | 7130 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 266),[(29868,1)]⟩
 | 7131 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 267),[(29869,1)]⟩
 | 7132 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 268),[(29871,1)]⟩
 | 7133 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 269),[(29870,4),(29871,1)]⟩
 | 7134 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 270),[(29872,1)]⟩
 | 7135 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 271),[(29873,1)]⟩
 | 7136 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 272),[(29875,1)]⟩
 | 7137 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 273),[(29874,4),(29875,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B10.count
