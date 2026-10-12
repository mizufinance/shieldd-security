import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0045
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 252).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9386 16
def localParent : Nat → Option Row
 | 9386 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 26),[(32124,1)]⟩
 | 9387 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 27),[(32125,1)]⟩
 | 9388 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 28),[(32127,1)]⟩
 | 9389 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 29),[(32126,4),(32127,1)]⟩
 | 9390 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 30),[(32128,1)]⟩
 | 9391 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 31),[(32129,1)]⟩
 | 9392 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 32),[(32131,1)]⟩
 | 9393 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 33),[(32130,4),(32131,1)]⟩
 | 9394 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 34),[(32132,1)]⟩
 | 9395 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 35),[(32133,1)]⟩
 | 9396 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 36),[(32135,1)]⟩
 | 9397 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 37),[(32134,4),(32135,1)]⟩
 | 9398 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 38),[(32136,1)]⟩
 | 9399 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 39),[(32137,1)]⟩
 | 9400 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 40),[(32139,1)]⟩
 | 9401 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 41),[(32138,4),(32139,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B19.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B19.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B19.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B19.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B19.count
