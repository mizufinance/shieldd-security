import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B11
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 124).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7138 16
def localParent : Nat → Option Row
 | 7138 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 274),[(29876,1)]⟩
 | 7139 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 275),[(29877,1)]⟩
 | 7140 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 276),[(29879,1)]⟩
 | 7141 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 277),[(29878,4),(29879,1)]⟩
 | 7142 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 278),[(29880,1)]⟩
 | 7143 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 279),[(29881,1)]⟩
 | 7144 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 280),[(29883,1)]⟩
 | 7145 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 281),[(29882,4),(29883,1)]⟩
 | 7146 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 282),[(29884,1)]⟩
 | 7147 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 283),[(29885,1)]⟩
 | 7148 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 284),[(29887,1)]⟩
 | 7149 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 285),[(29886,4),(29887,1)]⟩
 | 7150 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 286),[(29888,1)]⟩
 | 7151 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 287),[(29889,1)]⟩
 | 7152 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 288),[(29891,1)]⟩
 | 7153 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 289),[(29890,4),(29891,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B11

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B11.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B11.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B11.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B11.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B11.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B11.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B11.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B11.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B11.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B11.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B11.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B11.count
