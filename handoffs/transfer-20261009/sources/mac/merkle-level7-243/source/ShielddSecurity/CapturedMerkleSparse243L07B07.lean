import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0029
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6226 16
def localParent : Nat → Option Row
 | 6226 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 196),[(28964,1)]⟩
 | 6227 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 197),[(28965,1)]⟩
 | 6228 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 198),[(28967,1)]⟩
 | 6229 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 199),[(28966,4),(28967,1)]⟩
 | 6230 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 200),[(28968,1)]⟩
 | 6231 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 201),[(28969,1)]⟩
 | 6232 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 202),[(28971,1)]⟩
 | 6233 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 203),[(28970,4),(28971,1)]⟩
 | 6234 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 204),[(28972,1)]⟩
 | 6235 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 205),[(28973,1)]⟩
 | 6236 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 206),[(28975,1)]⟩
 | 6237 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 207),[(28974,4),(28975,1)]⟩
 | 6238 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 208),[(28976,1)]⟩
 | 6239 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 209),[(28977,1)]⟩
 | 6240 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 210),[(28979,1)]⟩
 | 6241 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0029.inputs 211),[(28978,4),(28979,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B07.count
