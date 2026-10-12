import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B04
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 12).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6602 16
def localParent : Nat → Option Row
 | 6602 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 154),[(29340,1)]⟩
 | 6603 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 155),[(29341,1)]⟩
 | 6604 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 156),[(29343,1)]⟩
 | 6605 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 157),[(29342,4),(29343,1)]⟩
 | 6606 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 158),[(29344,1)]⟩
 | 6607 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 159),[(29345,1)]⟩
 | 6608 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 160),[(29347,1)]⟩
 | 6609 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 161),[(29346,4),(29347,1)]⟩
 | 6610 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 162),[(29348,1)]⟩
 | 6611 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 163),[(29349,1)]⟩
 | 6612 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 164),[(29351,1)]⟩
 | 6613 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 165),[(29350,4),(29351,1)]⟩
 | 6614 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 166),[(29352,1)]⟩
 | 6615 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 167),[(29353,1)]⟩
 | 6616 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 168),[(29355,1)]⟩
 | 6617 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 169),[(29354,4),(29355,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B04

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B04.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B04.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B04.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B04.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B04.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B04.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B04.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B04.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B04.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B04.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B04.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B04.count
