import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0013
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstSparse245B16
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 216).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 424)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 2990 16
def localParent : Nat → Option Row
 | 2990 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 78),[(25728,1)]⟩
 | 2991 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 79),[(25729,1)]⟩
 | 2992 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 80),[(25731,1)]⟩
 | 2993 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 81),[(25730,4),(25731,1)]⟩
 | 2994 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 82),[(25732,1)]⟩
 | 2995 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 83),[(25733,1)]⟩
 | 2996 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 84),[(25735,1)]⟩
 | 2997 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 85),[(25734,4),(25735,1)]⟩
 | 2998 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 86),[(25736,1)]⟩
 | 2999 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 87),[(25737,1)]⟩
 | 3000 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 88),[(25739,1)]⟩
 | 3001 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 89),[(25738,4),(25739,1)]⟩
 | 3002 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 90),[(25740,1)]⟩
 | 3003 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 91),[(25741,1)]⟩
 | 3004 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 92),[(25743,1)]⟩
 | 3005 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0013.inputs 93),[(25742,4),(25743,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleFirstSparse245B16

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B16.rows
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B16.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B16.indices
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B16.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B16.localParent
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B16.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B16.localCheck
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B16.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B16.local_checked
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B16.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B16.count
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B16.count
