import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0014
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstSparse245B21
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 296).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 424)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3070 16
def localParent : Nat → Option Row
 | 3070 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 40),[(25808,1)]⟩
 | 3071 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 41),[(25809,1)]⟩
 | 3072 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 42),[(25811,1)]⟩
 | 3073 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 43),[(25810,4),(25811,1)]⟩
 | 3074 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 44),[(25812,1)]⟩
 | 3075 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 45),[(25813,1)]⟩
 | 3076 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 46),[(25815,1)]⟩
 | 3077 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 47),[(25814,4),(25815,1)]⟩
 | 3078 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 48),[(25816,1)]⟩
 | 3079 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 49),[(25817,1)]⟩
 | 3080 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 50),[(25819,1)]⟩
 | 3081 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 51),[(25818,4),(25819,1)]⟩
 | 3082 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 52),[(25820,1)]⟩
 | 3083 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 53),[(25821,1)]⟩
 | 3084 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 54),[(25823,1)]⟩
 | 3085 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 55),[(25822,4),(25823,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleFirstSparse245B21

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B21.rows
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B21.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B21.indices
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B21.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B21.localParent
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B21.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B21.localCheck
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B21.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B21.local_checked
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B21.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B21.count
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B21.count
