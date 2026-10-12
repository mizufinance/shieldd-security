import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0014
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstSparse245B22
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 312).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 424)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3086 16
def localParent : Nat → Option Row
 | 3086 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 56),[(25824,1)]⟩
 | 3087 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 57),[(25825,1)]⟩
 | 3088 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 58),[(25827,1)]⟩
 | 3089 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 59),[(25826,4),(25827,1)]⟩
 | 3090 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 60),[(25828,1)]⟩
 | 3091 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 61),[(25829,1)]⟩
 | 3092 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 62),[(25831,1)]⟩
 | 3093 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 63),[(25830,4),(25831,1)]⟩
 | 3094 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 64),[(25832,1)]⟩
 | 3095 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 65),[(25833,1)]⟩
 | 3096 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 66),[(25835,1)]⟩
 | 3097 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 67),[(25834,4),(25835,1)]⟩
 | 3098 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 68),[(25836,1)]⟩
 | 3099 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 69),[(25837,1)]⟩
 | 3100 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 70),[(25839,1)]⟩
 | 3101 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 71),[(25838,4),(25839,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleFirstSparse245B22

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B22.rows
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B22.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B22.indices
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B22.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B22.localParent
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B22.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B22.localCheck
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B22.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B22.local_checked
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B22.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B22.count
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B22.count
