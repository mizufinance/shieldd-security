import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0021
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4610 16
def localParent : Nat → Option Row
 | 4610 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 108),[(27348,1)]⟩
 | 4611 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 109),[(27349,1)]⟩
 | 4612 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 110),[(27351,1)]⟩
 | 4613 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 111),[(27350,4),(27351,1)]⟩
 | 4614 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 112),[(27352,1)]⟩
 | 4615 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 113),[(27353,1)]⟩
 | 4616 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 114),[(27355,1)]⟩
 | 4617 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 115),[(27354,4),(27355,1)]⟩
 | 4618 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 116),[(27356,1)]⟩
 | 4619 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 117),[(27357,1)]⟩
 | 4620 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 118),[(27359,1)]⟩
 | 4621 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 119),[(27358,4),(27359,1)]⟩
 | 4622 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 120),[(27360,1)]⟩
 | 4623 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 121),[(27361,1)]⟩
 | 4624 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 122),[(27363,1)]⟩
 | 4625 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0021.inputs 123),[(27362,4),(27363,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B12.count
