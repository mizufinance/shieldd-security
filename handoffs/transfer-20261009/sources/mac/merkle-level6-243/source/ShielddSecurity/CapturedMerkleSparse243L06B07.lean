import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L06B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3392)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5802 16
def localParent : Nat → Option Row
 | 5802 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 188),[(28540,1)]⟩
 | 5803 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 189),[(28541,1)]⟩
 | 5804 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 190),[(28543,1)]⟩
 | 5805 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 191),[(28542,4),(28543,1)]⟩
 | 5806 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 192),[(28544,1)]⟩
 | 5807 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 193),[(28545,1)]⟩
 | 5808 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 194),[(28547,1)]⟩
 | 5809 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 195),[(28546,4),(28547,1)]⟩
 | 5810 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 196),[(28548,1)]⟩
 | 5811 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 197),[(28549,1)]⟩
 | 5812 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 198),[(28551,1)]⟩
 | 5813 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 199),[(28550,4),(28551,1)]⟩
 | 5814 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 200),[(28552,1)]⟩
 | 5815 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 201),[(28553,1)]⟩
 | 5816 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 202),[(28555,1)]⟩
 | 5817 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 203),[(28554,4),(28555,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L06B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L06B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L06B07.count
