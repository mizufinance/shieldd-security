import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0040
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L12B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 5936)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 8442 16
def localParent : Nat → Option Row
 | 8442 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 51),[(31180,1)]⟩
 | 8443 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 52),[(31181,1)]⟩
 | 8444 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 53),[(31183,1)]⟩
 | 8445 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 54),[(31182,4),(31183,1)]⟩
 | 8446 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 55),[(31184,1)]⟩
 | 8447 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 56),[(31185,1)]⟩
 | 8448 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 57),[(31187,1)]⟩
 | 8449 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 58),[(31186,4),(31187,1)]⟩
 | 8450 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 59),[(31188,1)]⟩
 | 8451 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 60),[(31189,1)]⟩
 | 8452 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 61),[(31191,1)]⟩
 | 8453 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 62),[(31190,4),(31191,1)]⟩
 | 8454 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 63),[(31192,1)]⟩
 | 8455 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 64),[(31193,1)]⟩
 | 8456 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 65),[(31195,1)]⟩
 | 8457 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0040.inputs 66),[(31194,4),(31195,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L12B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L12B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L12B13.count
