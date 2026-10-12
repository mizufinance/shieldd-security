import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 316).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6058 16
def localParent : Nat → Option Row
 | 6058 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 28),[(28796,1)]⟩
 | 6059 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 29),[(28797,1)]⟩
 | 6060 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 30),[(28799,1)]⟩
 | 6061 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 31),[(28798,4),(28799,1)]⟩
 | 6062 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 32),[(28800,1)]⟩
 | 6063 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 33),[(28801,1)]⟩
 | 6064 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 34),[(28803,1)]⟩
 | 6065 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 35),[(28802,4),(28803,1)]⟩
 | 6066 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 36),[(28804,1)]⟩
 | 6067 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 37),[(28805,1)]⟩
 | 6068 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 38),[(28807,1)]⟩
 | 6069 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 39),[(28806,4),(28807,1)]⟩
 | 6070 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 40),[(28808,1)]⟩
 | 6071 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 41),[(28809,1)]⟩
 | 6072 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 42),[(28811,1)]⟩
 | 6073 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 43),[(28810,4),(28811,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B23.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B23.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B23.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B23.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B23.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B23.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B23.count
