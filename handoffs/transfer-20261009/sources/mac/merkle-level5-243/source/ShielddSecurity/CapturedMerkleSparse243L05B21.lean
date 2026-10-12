import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0026
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 284).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5602 16
def localParent : Nat → Option Row
 | 5602 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 80),[(28340,1)]⟩
 | 5603 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 81),[(28341,1)]⟩
 | 5604 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 82),[(28343,1)]⟩
 | 5605 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 83),[(28342,4),(28343,1)]⟩
 | 5606 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 84),[(28344,1)]⟩
 | 5607 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 85),[(28345,1)]⟩
 | 5608 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 86),[(28347,1)]⟩
 | 5609 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 87),[(28346,4),(28347,1)]⟩
 | 5610 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 88),[(28348,1)]⟩
 | 5611 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 89),[(28349,1)]⟩
 | 5612 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 90),[(28351,1)]⟩
 | 5613 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0026.inputs 91),[(28350,4),(28351,1)]⟩
 | 5614 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 0),[(28352,1)]⟩
 | 5615 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 1),[(28353,1)]⟩
 | 5616 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 2),[(28355,1)]⟩
 | 5617 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 3),[(28354,4),(28355,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B21.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B21.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B21.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B21.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B21.count
