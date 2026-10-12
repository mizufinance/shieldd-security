import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0045
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L14B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 6784)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 9370 16
def localParent : Nat → Option Row
 | 9370 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 10),[(32108,1)]⟩
 | 9371 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 11),[(32109,1)]⟩
 | 9372 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 12),[(32111,1)]⟩
 | 9373 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 13),[(32110,4),(32111,1)]⟩
 | 9374 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 14),[(32112,1)]⟩
 | 9375 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 15),[(32113,1)]⟩
 | 9376 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 16),[(32115,1)]⟩
 | 9377 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 17),[(32114,4),(32115,1)]⟩
 | 9378 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 18),[(32116,1)]⟩
 | 9379 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 19),[(32117,1)]⟩
 | 9380 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 20),[(32119,1)]⟩
 | 9381 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 21),[(32118,4),(32119,1)]⟩
 | 9382 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 22),[(32120,1)]⟩
 | 9383 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 23),[(32121,1)]⟩
 | 9384 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 24),[(32123,1)]⟩
 | 9385 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0045.inputs 25),[(32122,4),(32123,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L14B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L14B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L14B18.count
