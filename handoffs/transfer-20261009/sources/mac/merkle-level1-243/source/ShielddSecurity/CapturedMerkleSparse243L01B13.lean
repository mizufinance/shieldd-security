import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0017
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L01B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 1272)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3778 16
def localParent : Nat → Option Row
 | 3778 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 54),[(26516,1)]⟩
 | 3779 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 55),[(26517,1)]⟩
 | 3780 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 56),[(26519,1)]⟩
 | 3781 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 57),[(26518,4),(26519,1)]⟩
 | 3782 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 58),[(26520,1)]⟩
 | 3783 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 59),[(26521,1)]⟩
 | 3784 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 60),[(26523,1)]⟩
 | 3785 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 61),[(26522,4),(26523,1)]⟩
 | 3786 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 62),[(26524,1)]⟩
 | 3787 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 63),[(26525,1)]⟩
 | 3788 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 64),[(26527,1)]⟩
 | 3789 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 65),[(26526,4),(26527,1)]⟩
 | 3790 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 66),[(26528,1)]⟩
 | 3791 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 67),[(26529,1)]⟩
 | 3792 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 68),[(26531,1)]⟩
 | 3793 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0017.inputs 69),[(26530,4),(26531,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L01B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L01B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L01B13.count
