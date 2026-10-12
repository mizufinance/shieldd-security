import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0014
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstSparse245B23
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 328).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 424)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3102 16
def localParent : Nat → Option Row
 | 3102 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 72),[(25840,1)]⟩
 | 3103 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 73),[(25841,1)]⟩
 | 3104 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 74),[(25843,1)]⟩
 | 3105 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 75),[(25842,4),(25843,1)]⟩
 | 3106 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 76),[(25844,1)]⟩
 | 3107 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 77),[(25845,1)]⟩
 | 3108 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 78),[(25847,1)]⟩
 | 3109 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 79),[(25846,4),(25847,1)]⟩
 | 3110 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 80),[(25848,1)]⟩
 | 3111 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 81),[(25849,1)]⟩
 | 3112 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 82),[(25851,1)]⟩
 | 3113 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 83),[(25850,4),(25851,1)]⟩
 | 3114 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 84),[(25852,1)]⟩
 | 3115 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 85),[(25853,1)]⟩
 | 3116 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 86),[(25855,1)]⟩
 | 3117 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 87),[(25854,4),(25855,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleFirstSparse245B23

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B23.rows
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B23.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B23.indices
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B23.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B23.localParent
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B23.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B23.localCheck
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B23.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B23.local_checked
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B23.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B23.count
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B23.count
