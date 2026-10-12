import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0026
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 204).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5522 16
def localParent : Nat → Option Row
 | 5522 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 0),[(28260,1)]⟩
 | 5523 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 1),[(28261,1)]⟩
 | 5524 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 2),[(28263,1)]⟩
 | 5525 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 3),[(28262,4),(28263,1)]⟩
 | 5526 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 4),[(28264,1)]⟩
 | 5527 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 5),[(28265,1)]⟩
 | 5528 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 6),[(28267,1)]⟩
 | 5529 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 7),[(28266,4),(28267,1)]⟩
 | 5530 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 8),[(28268,1)]⟩
 | 5531 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 9),[(28269,1)]⟩
 | 5532 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 10),[(28271,1)]⟩
 | 5533 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 11),[(28270,4),(28271,1)]⟩
 | 5534 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 12),[(28272,1)]⟩
 | 5535 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 13),[(28273,1)]⟩
 | 5536 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 14),[(28275,1)]⟩
 | 5537 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 15),[(28274,4),(28275,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B16.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B16.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B16.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B16.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B16.count
