import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0014
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L00B06
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 44).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 848)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3242 16
def localParent : Nat → Option Row
 | 3242 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 212),[(25980,1)]⟩
 | 3243 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 213),[(25981,1)]⟩
 | 3244 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 214),[(25983,1)]⟩
 | 3245 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 215),[(25982,4),(25983,1)]⟩
 | 3246 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 216),[(25984,1)]⟩
 | 3247 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 217),[(25985,1)]⟩
 | 3248 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 218),[(25987,1)]⟩
 | 3249 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 219),[(25986,4),(25987,1)]⟩
 | 3250 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 220),[(25988,1)]⟩
 | 3251 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 221),[(25989,1)]⟩
 | 3252 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 222),[(25991,1)]⟩
 | 3253 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 223),[(25990,4),(25991,1)]⟩
 | 3254 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 224),[(25992,1)]⟩
 | 3255 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 225),[(25993,1)]⟩
 | 3256 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 226),[(25995,1)]⟩
 | 3257 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 227),[(25994,4),(25995,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L00B06

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B06.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B06.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B06.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B06.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B06.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B06.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B06.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B06.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B06.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B06.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L00B06.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L00B06.count
