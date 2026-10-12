import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0015
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3386 16
def localParent : Nat → Option Row
 | 3386 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 66),[(26124,1)]⟩
 | 3387 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 67),[(26125,1)]⟩
 | 3388 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 68),[(26127,1)]⟩
 | 3389 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 69),[(26126,4),(26127,1)]⟩
 | 3390 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 70),[(26128,1)]⟩
 | 3391 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 71),[(26129,1)]⟩
 | 3392 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 72),[(26131,1)]⟩
 | 3393 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 73),[(26130,4),(26131,1)]⟩
 | 3394 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 74),[(26132,1)]⟩
 | 3395 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 75),[(26133,1)]⟩
 | 3396 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 76),[(26135,1)]⟩
 | 3397 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 77),[(26134,4),(26135,1)]⟩
 | 3398 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 78),[(26136,1)]⟩
 | 3399 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 79),[(26137,1)]⟩
 | 3400 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 80),[(26139,1)]⟩
 | 3401 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0015.inputs 81),[(26138,4),(26139,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B15.count
