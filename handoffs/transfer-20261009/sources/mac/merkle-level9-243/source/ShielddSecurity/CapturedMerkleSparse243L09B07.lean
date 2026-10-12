import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0033
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L09B07
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 60).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4664)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 7074 16
def localParent : Nat → Option Row
 | 7074 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 210),[(29812,1)]⟩
 | 7075 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 211),[(29813,1)]⟩
 | 7076 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 212),[(29815,1)]⟩
 | 7077 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 213),[(29814,4),(29815,1)]⟩
 | 7078 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 214),[(29816,1)]⟩
 | 7079 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 215),[(29817,1)]⟩
 | 7080 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 216),[(29819,1)]⟩
 | 7081 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 217),[(29818,4),(29819,1)]⟩
 | 7082 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 218),[(29820,1)]⟩
 | 7083 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 219),[(29821,1)]⟩
 | 7084 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 220),[(29823,1)]⟩
 | 7085 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 221),[(29822,4),(29823,1)]⟩
 | 7086 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 222),[(29824,1)]⟩
 | 7087 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 223),[(29825,1)]⟩
 | 7088 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 224),[(29827,1)]⟩
 | 7089 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0033.inputs 225),[(29826,4),(29827,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L09B07

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B07.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B07.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B07.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B07.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B07.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B07.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B07.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B07.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B07.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B07.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L09B07.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L09B07.count
