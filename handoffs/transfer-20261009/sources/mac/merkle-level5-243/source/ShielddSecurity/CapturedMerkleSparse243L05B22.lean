import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0027
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L05B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 300).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2968)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 5618 16
def localParent : Nat → Option Row
 | 5618 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 4),[(28356,1)]⟩
 | 5619 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 5),[(28357,1)]⟩
 | 5620 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 6),[(28359,1)]⟩
 | 5621 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 7),[(28358,4),(28359,1)]⟩
 | 5622 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 8),[(28360,1)]⟩
 | 5623 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 9),[(28361,1)]⟩
 | 5624 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 10),[(28363,1)]⟩
 | 5625 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 11),[(28362,4),(28363,1)]⟩
 | 5626 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 12),[(28364,1)]⟩
 | 5627 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 13),[(28365,1)]⟩
 | 5628 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 14),[(28367,1)]⟩
 | 5629 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 15),[(28366,4),(28367,1)]⟩
 | 5630 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 16),[(28368,1)]⟩
 | 5631 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 17),[(28369,1)]⟩
 | 5632 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 18),[(28371,1)]⟩
 | 5633 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0027.inputs 19),[(28370,4),(28371,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L05B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B22.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B22.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B22.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L05B22.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L05B22.count
