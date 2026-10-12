import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B08
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 76).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6666 16
def localParent : Nat → Option Row
 | 6666 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 218),[(29404,1)]⟩
 | 6667 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 219),[(29405,1)]⟩
 | 6668 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 220),[(29407,1)]⟩
 | 6669 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 221),[(29406,4),(29407,1)]⟩
 | 6670 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 222),[(29408,1)]⟩
 | 6671 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 223),[(29409,1)]⟩
 | 6672 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 224),[(29411,1)]⟩
 | 6673 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 225),[(29410,4),(29411,1)]⟩
 | 6674 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 226),[(29412,1)]⟩
 | 6675 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 227),[(29413,1)]⟩
 | 6676 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 228),[(29415,1)]⟩
 | 6677 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 229),[(29414,4),(29415,1)]⟩
 | 6678 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 230),[(29416,1)]⟩
 | 6679 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 231),[(29417,1)]⟩
 | 6680 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 232),[(29419,1)]⟩
 | 6681 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 233),[(29418,4),(29419,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B08

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B08.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B08.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B08.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B08.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B08.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B08.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B08.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B08.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B08.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B08.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B08.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B08.count
