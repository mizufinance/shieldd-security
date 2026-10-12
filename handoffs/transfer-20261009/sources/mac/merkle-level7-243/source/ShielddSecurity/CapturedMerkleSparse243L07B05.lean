import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6194 16
def localParent : Nat → Option Row
 | 6194 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 164),[(28932,1)]⟩
 | 6195 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 165),[(28933,1)]⟩
 | 6196 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 166),[(28935,1)]⟩
 | 6197 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 167),[(28934,4),(28935,1)]⟩
 | 6198 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 168),[(28936,1)]⟩
 | 6199 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 169),[(28937,1)]⟩
 | 6200 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 170),[(28939,1)]⟩
 | 6201 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 171),[(28938,4),(28939,1)]⟩
 | 6202 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 172),[(28940,1)]⟩
 | 6203 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 173),[(28941,1)]⟩
 | 6204 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 174),[(28943,1)]⟩
 | 6205 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 175),[(28942,4),(28943,1)]⟩
 | 6206 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 176),[(28944,1)]⟩
 | 6207 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 177),[(28945,1)]⟩
 | 6208 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 178),[(28947,1)]⟩
 | 6209 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 179),[(28946,4),(28947,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B05.count
