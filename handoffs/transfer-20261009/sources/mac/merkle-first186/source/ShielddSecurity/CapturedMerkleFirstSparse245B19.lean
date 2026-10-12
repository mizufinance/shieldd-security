import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0014
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstSparse245B19
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 264).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 424)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3038 16
def localParent : Nat → Option Row
 | 3038 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 8),[(25776,1)]⟩
 | 3039 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 9),[(25777,1)]⟩
 | 3040 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 10),[(25779,1)]⟩
 | 3041 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 11),[(25778,4),(25779,1)]⟩
 | 3042 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 12),[(25780,1)]⟩
 | 3043 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 13),[(25781,1)]⟩
 | 3044 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 14),[(25783,1)]⟩
 | 3045 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 15),[(25782,4),(25783,1)]⟩
 | 3046 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 16),[(25784,1)]⟩
 | 3047 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 17),[(25785,1)]⟩
 | 3048 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 18),[(25787,1)]⟩
 | 3049 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 19),[(25786,4),(25787,1)]⟩
 | 3050 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 20),[(25788,1)]⟩
 | 3051 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 21),[(25789,1)]⟩
 | 3052 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 22),[(25791,1)]⟩
 | 3053 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 23),[(25790,4),(25791,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleFirstSparse245B19

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B19.rows
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B19.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B19.indices
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B19.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B19.localParent
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B19.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B19.localCheck
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B19.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B19.local_checked
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B19.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B19.count
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B19.count
