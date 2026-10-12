import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B12
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 140).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6730 16
def localParent : Nat → Option Row
 | 6730 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 282),[(29468,1)]⟩
 | 6731 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 283),[(29469,1)]⟩
 | 6732 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 284),[(29471,1)]⟩
 | 6733 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 285),[(29470,4),(29471,1)]⟩
 | 6734 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 286),[(29472,1)]⟩
 | 6735 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 287),[(29473,1)]⟩
 | 6736 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 288),[(29475,1)]⟩
 | 6737 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 289),[(29474,4),(29475,1)]⟩
 | 6738 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 290),[(29476,1)]⟩
 | 6739 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 291),[(29477,1)]⟩
 | 6740 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 292),[(29479,1)]⟩
 | 6741 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 293),[(29478,4),(29479,1)]⟩
 | 6742 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 294),[(29480,1)]⟩
 | 6743 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 295),[(29481,1)]⟩
 | 6744 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 296),[(29483,1)]⟩
 | 6745 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 297),[(29482,4),(29483,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B12

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B12.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B12.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B12.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B12.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B12.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B12.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B12.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B12.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B12.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B12.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B12.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B12.count
