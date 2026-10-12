import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0031
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleSparse243L07B26
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 364).take 8).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 3816)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 6530 8
def localParent : Nat → Option Row
 | 6530 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 82),[(29268,1)]⟩
 | 6531 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 83),[(29269,1)]⟩
 | 6532 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 84),[(29271,1)]⟩
 | 6533 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 85),[(29270,4),(29271,1)]⟩
 | 6534 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 86),[(29272,1)]⟩
 | 6535 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 87),[(29273,1)]⟩
 | 6536 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 88),[(29275,1)]⟩
 | 6537 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0031.inputs 89),[(29274,4),(29275,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=8 := by rfl
end ShielddSecurity.CapturedMerkleSparse243L07B26

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B26.rows
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B26.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B26.indices
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B26.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B26.localParent
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B26.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B26.localCheck
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B26.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B26.local_checked
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B26.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleSparse243L07B26.count
#print axioms ShielddSecurity.CapturedMerkleSparse243L07B26.count
