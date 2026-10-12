import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 348).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5666 16
def localParent : Nat → Option Row
 | 5666 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 52),[(28404,1)]⟩
 | 5667 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 53),[(28405,1)]⟩
 | 5668 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 54),[(28407,1)]⟩
 | 5669 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 55),[(28406,4),(28407,1)]⟩
 | 5670 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 56),[(28408,1)]⟩
 | 5671 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 57),[(28409,1)]⟩
 | 5672 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 58),[(28411,1)]⟩
 | 5673 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 59),[(28410,4),(28411,1)]⟩
 | 5674 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 60),[(28412,1)]⟩
 | 5675 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 61),[(28413,1)]⟩
 | 5676 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 62),[(28415,1)]⟩
 | 5677 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 63),[(28414,4),(28415,1)]⟩
 | 5678 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 64),[(28416,1)]⟩
 | 5679 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 65),[(28417,1)]⟩
 | 5680 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 66),[(28419,1)]⟩
 | 5681 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 67),[(28418,4),(28419,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B25.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B25.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B25.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B25.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B25.count
