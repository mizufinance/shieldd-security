import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B09
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 92).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6258 16
def localParent : Nat → Option Row
 | 6258 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 228),[(28996,1)]⟩
 | 6259 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 229),[(28997,1)]⟩
 | 6260 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 230),[(28999,1)]⟩
 | 6261 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 231),[(28998,4),(28999,1)]⟩
 | 6262 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 232),[(29000,1)]⟩
 | 6263 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 233),[(29001,1)]⟩
 | 6264 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 234),[(29003,1)]⟩
 | 6265 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 235),[(29002,4),(29003,1)]⟩
 | 6266 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 236),[(29004,1)]⟩
 | 6267 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 237),[(29005,1)]⟩
 | 6268 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 238),[(29007,1)]⟩
 | 6269 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 239),[(29006,4),(29007,1)]⟩
 | 6270 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 240),[(29008,1)]⟩
 | 6271 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 241),[(29009,1)]⟩
 | 6272 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 242),[(29011,1)]⟩
 | 6273 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 243),[(29010,4),(29011,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B09

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B09.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B09.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B09.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B09.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B09.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B09.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B09.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B09.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B09.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B09.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B09.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B09.count
