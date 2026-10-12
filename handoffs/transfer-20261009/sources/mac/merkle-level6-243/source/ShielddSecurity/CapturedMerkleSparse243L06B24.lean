import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B24
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 332).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6074 16
def localParent : Nat → Option Row
 | 6074 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 44),[(28812,1)]⟩
 | 6075 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 45),[(28813,1)]⟩
 | 6076 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 46),[(28815,1)]⟩
 | 6077 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 47),[(28814,4),(28815,1)]⟩
 | 6078 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 48),[(28816,1)]⟩
 | 6079 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 49),[(28817,1)]⟩
 | 6080 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 50),[(28819,1)]⟩
 | 6081 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 51),[(28818,4),(28819,1)]⟩
 | 6082 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 52),[(28820,1)]⟩
 | 6083 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 53),[(28821,1)]⟩
 | 6084 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 54),[(28823,1)]⟩
 | 6085 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 55),[(28822,4),(28823,1)]⟩
 | 6086 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 56),[(28824,1)]⟩
 | 6087 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 57),[(28825,1)]⟩
 | 6088 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 58),[(28827,1)]⟩
 | 6089 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 59),[(28826,4),(28827,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B24

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B24.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B24.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B24.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B24.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B24.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B24.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B24.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B24.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B24.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B24.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B24.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B24.count
