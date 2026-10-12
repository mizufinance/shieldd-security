import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B05
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 28).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7042 16
def localParent : Nat → Option Row
 | 7042 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 178),[(29780,1)]⟩
 | 7043 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 179),[(29781,1)]⟩
 | 7044 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 180),[(29783,1)]⟩
 | 7045 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 181),[(29782,4),(29783,1)]⟩
 | 7046 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 182),[(29784,1)]⟩
 | 7047 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 183),[(29785,1)]⟩
 | 7048 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 184),[(29787,1)]⟩
 | 7049 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 185),[(29786,4),(29787,1)]⟩
 | 7050 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 186),[(29788,1)]⟩
 | 7051 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 187),[(29789,1)]⟩
 | 7052 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 188),[(29791,1)]⟩
 | 7053 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 189),[(29790,4),(29791,1)]⟩
 | 7054 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 190),[(29792,1)]⟩
 | 7055 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 191),[(29793,1)]⟩
 | 7056 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 192),[(29795,1)]⟩
 | 7057 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 193),[(29794,4),(29795,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B05

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B05.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B05.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B05.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B05.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B05.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B05.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B05.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B05.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B05.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B05.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B05.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B05.count
