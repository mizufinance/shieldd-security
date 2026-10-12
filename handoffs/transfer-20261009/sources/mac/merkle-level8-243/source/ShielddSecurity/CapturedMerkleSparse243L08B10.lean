import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L08B10
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 108).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 4240)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6698 16
def localParent : Nat → Option Row
 | 6698 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 250),[(29436,1)]⟩
 | 6699 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 251),[(29437,1)]⟩
 | 6700 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 252),[(29439,1)]⟩
 | 6701 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 253),[(29438,4),(29439,1)]⟩
 | 6702 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 254),[(29440,1)]⟩
 | 6703 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 255),[(29441,1)]⟩
 | 6704 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 256),[(29443,1)]⟩
 | 6705 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 257),[(29442,4),(29443,1)]⟩
 | 6706 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 258),[(29444,1)]⟩
 | 6707 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 259),[(29445,1)]⟩
 | 6708 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 260),[(29447,1)]⟩
 | 6709 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 261),[(29446,4),(29447,1)]⟩
 | 6710 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 262),[(29448,1)]⟩
 | 6711 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 263),[(29449,1)]⟩
 | 6712 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 264),[(29451,1)]⟩
 | 6713 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 265),[(29450,4),(29451,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L08B10

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B10.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B10.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B10.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B10.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B10.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B10.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B10.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B10.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B10.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B10.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L08B10.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L08B10.count
