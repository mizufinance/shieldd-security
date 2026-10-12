import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0034
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B17
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 220).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7234 16
def localParent : Nat → Option Row
 | 7234 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 64),[(29972,1)]⟩
 | 7235 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 65),[(29973,1)]⟩
 | 7236 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 66),[(29975,1)]⟩
 | 7237 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 67),[(29974,4),(29975,1)]⟩
 | 7238 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 68),[(29976,1)]⟩
 | 7239 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 69),[(29977,1)]⟩
 | 7240 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 70),[(29979,1)]⟩
 | 7241 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 71),[(29978,4),(29979,1)]⟩
 | 7242 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 72),[(29980,1)]⟩
 | 7243 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 73),[(29981,1)]⟩
 | 7244 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 74),[(29983,1)]⟩
 | 7245 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 75),[(29982,4),(29983,1)]⟩
 | 7246 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 76),[(29984,1)]⟩
 | 7247 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 77),[(29985,1)]⟩
 | 7248 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 78),[(29987,1)]⟩
 | 7249 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0034.inputs 79),[(29986,4),(29987,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B17

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B17.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B17.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B17.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B17.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B17.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B17.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B17.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B17.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B17.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B17.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B17.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B17.count
