import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0041
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 316).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8602 16
def localParent : Nat → Option Row
 | 8602 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 74),[(31340,1)]⟩
 | 8603 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 75),[(31341,1)]⟩
 | 8604 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 76),[(31343,1)]⟩
 | 8605 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 77),[(31342,4),(31343,1)]⟩
 | 8606 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 78),[(31344,1)]⟩
 | 8607 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 79),[(31345,1)]⟩
 | 8608 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 80),[(31347,1)]⟩
 | 8609 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 81),[(31346,4),(31347,1)]⟩
 | 8610 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 82),[(31348,1)]⟩
 | 8611 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 83),[(31349,1)]⟩
 | 8612 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 84),[(31351,1)]⟩
 | 8613 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 85),[(31350,4),(31351,1)]⟩
 | 8614 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 86),[(31352,1)]⟩
 | 8615 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 87),[(31353,1)]⟩
 | 8616 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 88),[(31355,1)]⟩
 | 8617 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0041.inputs 89),[(31354,4),(31355,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B23.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B23.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B23.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B23.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B23.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B23.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B23.count
