import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0043
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L13B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 300).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6360)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9010 16
def localParent : Nat → Option Row
 | 9010 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 66),[(31748,1)]⟩
 | 9011 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 67),[(31749,1)]⟩
 | 9012 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 68),[(31751,1)]⟩
 | 9013 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 69),[(31750,4),(31751,1)]⟩
 | 9014 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 70),[(31752,1)]⟩
 | 9015 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 71),[(31753,1)]⟩
 | 9016 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 72),[(31755,1)]⟩
 | 9017 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 73),[(31754,4),(31755,1)]⟩
 | 9018 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 74),[(31756,1)]⟩
 | 9019 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 75),[(31757,1)]⟩
 | 9020 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 76),[(31759,1)]⟩
 | 9021 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 77),[(31758,4),(31759,1)]⟩
 | 9022 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 78),[(31760,1)]⟩
 | 9023 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 79),[(31761,1)]⟩
 | 9024 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 80),[(31763,1)]⟩
 | 9025 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0043.inputs 81),[(31762,4),(31763,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L13B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B22.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B22.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B22.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L13B22.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L13B22.count
