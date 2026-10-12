import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0030
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6402 16
def localParent : Nat → Option Row
 | 6402 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 54),[(29140,1)]⟩
 | 6403 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 55),[(29141,1)]⟩
 | 6404 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 56),[(29143,1)]⟩
 | 6405 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 57),[(29142,4),(29143,1)]⟩
 | 6406 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 58),[(29144,1)]⟩
 | 6407 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 59),[(29145,1)]⟩
 | 6408 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 60),[(29147,1)]⟩
 | 6409 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 61),[(29146,4),(29147,1)]⟩
 | 6410 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 62),[(29148,1)]⟩
 | 6411 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 63),[(29149,1)]⟩
 | 6412 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 64),[(29151,1)]⟩
 | 6413 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 65),[(29150,4),(29151,1)]⟩
 | 6414 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 66),[(29152,1)]⟩
 | 6415 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 67),[(29153,1)]⟩
 | 6416 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 68),[(29155,1)]⟩
 | 6417 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0030.inputs 69),[(29154,4),(29155,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B18.count
