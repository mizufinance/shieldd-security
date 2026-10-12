import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0034
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B15
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 188).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7202 16
def localParent : Nat → Option Row
 | 7202 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 32),[(29940,1)]⟩
 | 7203 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 33),[(29941,1)]⟩
 | 7204 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 34),[(29943,1)]⟩
 | 7205 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 35),[(29942,4),(29943,1)]⟩
 | 7206 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 36),[(29944,1)]⟩
 | 7207 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 37),[(29945,1)]⟩
 | 7208 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 38),[(29947,1)]⟩
 | 7209 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 39),[(29946,4),(29947,1)]⟩
 | 7210 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 40),[(29948,1)]⟩
 | 7211 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 41),[(29949,1)]⟩
 | 7212 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 42),[(29951,1)]⟩
 | 7213 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 43),[(29950,4),(29951,1)]⟩
 | 7214 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 44),[(29952,1)]⟩
 | 7215 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 45),[(29953,1)]⟩
 | 7216 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 46),[(29955,1)]⟩
 | 7217 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 47),[(29954,4),(29955,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B15

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B15.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B15.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B15.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B15.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B15.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B15.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B15.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B15.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B15.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B15.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B15.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B15.count
