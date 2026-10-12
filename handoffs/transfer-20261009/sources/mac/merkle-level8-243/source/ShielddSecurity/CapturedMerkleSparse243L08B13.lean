import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CapturedArithmetic45B0032
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B13
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 156).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6746 16
def localParent : Nat → Option Row
 | 6746 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 298),[(29484,1)]⟩
 | 6747 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 299),[(29485,1)]⟩
 | 6748 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 300),[(29487,1)]⟩
 | 6749 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 301),[(29486,4),(29487,1)]⟩
 | 6750 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 302),[(29488,1)]⟩
 | 6751 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 303),[(29489,1)]⟩
 | 6752 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 304),[(29491,1)]⟩
 | 6753 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 305),[(29490,4),(29491,1)]⟩
 | 6754 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 306),[(29492,1)]⟩
 | 6755 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 307),[(29493,1)]⟩
 | 6756 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 308),[(29495,1)]⟩
 | 6757 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 309),[(29494,4),(29495,1)]⟩
 | 6758 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 310),[(29496,1)]⟩
 | 6759 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 311),[(29497,1)]⟩
 | 6760 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 0),[(29499,1)]⟩
 | 6761 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0032.inputs 1),[(29498,4),(29499,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B13

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B13.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B13.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B13.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B13.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B13.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B13.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B13.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B13.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B13.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B13.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B13.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B13.count
