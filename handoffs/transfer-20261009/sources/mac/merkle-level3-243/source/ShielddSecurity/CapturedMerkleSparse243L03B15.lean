import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0021
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4658 16
def localParent : Nat → Option Row
 | 4658 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 156),[(27396,1)]⟩
 | 4659 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 157),[(27397,1)]⟩
 | 4660 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 158),[(27399,1)]⟩
 | 4661 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 159),[(27398,4),(27399,1)]⟩
 | 4662 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 160),[(27400,1)]⟩
 | 4663 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 161),[(27401,1)]⟩
 | 4664 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 162),[(27403,1)]⟩
 | 4665 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 163),[(27402,4),(27403,1)]⟩
 | 4666 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 164),[(27404,1)]⟩
 | 4667 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 165),[(27405,1)]⟩
 | 4668 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 166),[(27407,1)]⟩
 | 4669 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 167),[(27406,4),(27407,1)]⟩
 | 4670 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 168),[(27408,1)]⟩
 | 4671 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 169),[(27409,1)]⟩
 | 4672 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 170),[(27411,1)]⟩
 | 4673 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 171),[(27410,4),(27411,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B15.count
