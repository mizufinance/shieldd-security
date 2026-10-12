import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0014
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstSparse245B25
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 360).take 12).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 424)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3134 12
def localParent : Nat → Option Row
 | 3134 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 104),[(25872,1)]⟩
 | 3135 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 105),[(25873,1)]⟩
 | 3136 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 106),[(25875,1)]⟩
 | 3137 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 107),[(25874,4),(25875,1)]⟩
 | 3138 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 108),[(25876,1)]⟩
 | 3139 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 109),[(25877,1)]⟩
 | 3140 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 110),[(25879,1)]⟩
 | 3141 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 111),[(25878,4),(25879,1)]⟩
 | 3142 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 112),[(25880,1)]⟩
 | 3143 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 113),[(25881,1)]⟩
 | 3144 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 114),[(25883,1)]⟩
 | 3145 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 115),[(25882,4),(25883,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=12 := by rfl
end ShielddSecurity.CapturedMerkleFirstSparse245B25

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B25.rows
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B25.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B25.indices
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B25.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B25.localParent
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B25.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B25.localCheck
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B25.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B25.local_checked
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B25.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B25.count
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B25.count
