import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0014
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3210 16
def localParent : Nat → Option Row
 | 3210 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 180),[(25948,1)]⟩
 | 3211 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 181),[(25949,1)]⟩
 | 3212 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 182),[(25951,1)]⟩
 | 3213 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 183),[(25950,4),(25951,1)]⟩
 | 3214 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 184),[(25952,1)]⟩
 | 3215 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 185),[(25953,1)]⟩
 | 3216 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 186),[(25955,1)]⟩
 | 3217 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 187),[(25954,4),(25955,1)]⟩
 | 3218 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 188),[(25956,1)]⟩
 | 3219 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 189),[(25957,1)]⟩
 | 3220 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 190),[(25959,1)]⟩
 | 3221 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 191),[(25958,4),(25959,1)]⟩
 | 3222 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 192),[(25960,1)]⟩
 | 3223 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 193),[(25961,1)]⟩
 | 3224 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 194),[(25963,1)]⟩
 | 3225 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 195),[(25962,4),(25963,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B04.count
