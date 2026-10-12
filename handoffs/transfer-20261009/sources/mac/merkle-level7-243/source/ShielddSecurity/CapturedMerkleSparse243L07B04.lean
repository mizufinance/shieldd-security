import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6178 16
def localParent : Nat → Option Row
 | 6178 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 148),[(28916,1)]⟩
 | 6179 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 149),[(28917,1)]⟩
 | 6180 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 150),[(28919,1)]⟩
 | 6181 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 151),[(28918,4),(28919,1)]⟩
 | 6182 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 152),[(28920,1)]⟩
 | 6183 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 153),[(28921,1)]⟩
 | 6184 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 154),[(28923,1)]⟩
 | 6185 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 155),[(28922,4),(28923,1)]⟩
 | 6186 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 156),[(28924,1)]⟩
 | 6187 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 157),[(28925,1)]⟩
 | 6188 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 158),[(28927,1)]⟩
 | 6189 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 159),[(28926,4),(28927,1)]⟩
 | 6190 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 160),[(28928,1)]⟩
 | 6191 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 161),[(28929,1)]⟩
 | 6192 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 162),[(28931,1)]⟩
 | 6193 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 163),[(28930,4),(28931,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B04.count
