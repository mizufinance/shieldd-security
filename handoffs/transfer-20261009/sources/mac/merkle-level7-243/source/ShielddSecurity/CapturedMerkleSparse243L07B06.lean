import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6210 16
def localParent : Nat → Option Row
 | 6210 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 180),[(28948,1)]⟩
 | 6211 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 181),[(28949,1)]⟩
 | 6212 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 182),[(28951,1)]⟩
 | 6213 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 183),[(28950,4),(28951,1)]⟩
 | 6214 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 184),[(28952,1)]⟩
 | 6215 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 185),[(28953,1)]⟩
 | 6216 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 186),[(28955,1)]⟩
 | 6217 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 187),[(28954,4),(28955,1)]⟩
 | 6218 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 188),[(28956,1)]⟩
 | 6219 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 189),[(28957,1)]⟩
 | 6220 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 190),[(28959,1)]⟩
 | 6221 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 191),[(28958,4),(28959,1)]⟩
 | 6222 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 192),[(28960,1)]⟩
 | 6223 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 193),[(28961,1)]⟩
 | 6224 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 194),[(28963,1)]⟩
 | 6225 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 195),[(28962,4),(28963,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B06.count
