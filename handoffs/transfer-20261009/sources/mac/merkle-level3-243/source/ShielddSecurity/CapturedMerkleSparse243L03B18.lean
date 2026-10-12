import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0022
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L03B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 236).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 2120)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 4706 16
def localParent : Nat → Option Row
 | 4706 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 12),[(27444,1)]⟩
 | 4707 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 13),[(27445,1)]⟩
 | 4708 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 14),[(27447,1)]⟩
 | 4709 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 15),[(27446,4),(27447,1)]⟩
 | 4710 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 16),[(27448,1)]⟩
 | 4711 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 17),[(27449,1)]⟩
 | 4712 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 18),[(27451,1)]⟩
 | 4713 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 19),[(27450,4),(27451,1)]⟩
 | 4714 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 20),[(27452,1)]⟩
 | 4715 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 21),[(27453,1)]⟩
 | 4716 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 22),[(27455,1)]⟩
 | 4717 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 23),[(27454,4),(27455,1)]⟩
 | 4718 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 24),[(27456,1)]⟩
 | 4719 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 25),[(27457,1)]⟩
 | 4720 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 26),[(27459,1)]⟩
 | 4721 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0022.inputs 27),[(27458,4),(27459,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L03B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B18.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B18.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B18.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L03B18.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L03B18.count
