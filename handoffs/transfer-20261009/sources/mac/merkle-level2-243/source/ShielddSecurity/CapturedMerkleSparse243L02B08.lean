import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0019
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L02B08
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 76).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1696)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4122 16
def localParent : Nat → Option Row
 | 4122 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 0),[(26860,1)]⟩
 | 4123 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 1),[(26861,1)]⟩
 | 4124 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 2),[(26863,1)]⟩
 | 4125 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 3),[(26862,4),(26863,1)]⟩
 | 4126 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 4),[(26864,1)]⟩
 | 4127 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 5),[(26865,1)]⟩
 | 4128 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 6),[(26867,1)]⟩
 | 4129 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 7),[(26866,4),(26867,1)]⟩
 | 4130 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 8),[(26868,1)]⟩
 | 4131 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 9),[(26869,1)]⟩
 | 4132 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 10),[(26871,1)]⟩
 | 4133 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 11),[(26870,4),(26871,1)]⟩
 | 4134 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 12),[(26872,1)]⟩
 | 4135 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 13),[(26873,1)]⟩
 | 4136 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 14),[(26875,1)]⟩
 | 4137 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0019.inputs 15),[(26874,4),(26875,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L02B08

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B08.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B08.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B08.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B08.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B08.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B08.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B08.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B08.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L02B08.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L02B08.count
