import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0013
import ShielddSecurity.CapturedArithmetic45B0014
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstSparse245B18
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 248).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 424)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3022 16
def localParent : Nat → Option Row
 | 3022 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 110),[(25760,1)]⟩
 | 3023 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 111),[(25761,1)]⟩
 | 3024 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 112),[(25763,1)]⟩
 | 3025 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 113),[(25762,4),(25763,1)]⟩
 | 3026 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 114),[(25764,1)]⟩
 | 3027 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 115),[(25765,1)]⟩
 | 3028 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 116),[(25767,1)]⟩
 | 3029 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 117),[(25766,4),(25767,1)]⟩
 | 3030 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 0),[(25768,1)]⟩
 | 3031 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 1),[(25769,1)]⟩
 | 3032 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 2),[(25771,1)]⟩
 | 3033 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 3),[(25770,4),(25771,1)]⟩
 | 3034 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 4),[(25772,1)]⟩
 | 3035 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 5),[(25773,1)]⟩
 | 3036 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 6),[(25775,1)]⟩
 | 3037 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 7),[(25774,4),(25775,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleFirstSparse245B18

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B18.rows
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B18.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B18.indices
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B18.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B18.localParent
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B18.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B18.localCheck
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B18.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B18.local_checked
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B18.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B18.count
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B18.count
