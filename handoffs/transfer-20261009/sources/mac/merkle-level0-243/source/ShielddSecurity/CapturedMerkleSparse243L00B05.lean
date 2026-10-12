import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0014
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3226 16
def localParent : Nat → Option Row
 | 3226 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 196),[(25964,1)]⟩
 | 3227 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 197),[(25965,1)]⟩
 | 3228 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 198),[(25967,1)]⟩
 | 3229 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 199),[(25966,4),(25967,1)]⟩
 | 3230 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 200),[(25968,1)]⟩
 | 3231 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 201),[(25969,1)]⟩
 | 3232 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 202),[(25971,1)]⟩
 | 3233 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 203),[(25970,4),(25971,1)]⟩
 | 3234 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 204),[(25972,1)]⟩
 | 3235 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 205),[(25973,1)]⟩
 | 3236 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 206),[(25975,1)]⟩
 | 3237 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 207),[(25974,4),(25975,1)]⟩
 | 3238 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 208),[(25976,1)]⟩
 | 3239 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 209),[(25977,1)]⟩
 | 3240 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 210),[(25979,1)]⟩
 | 3241 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 211),[(25978,4),(25979,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B05.count
