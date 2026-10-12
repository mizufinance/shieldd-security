import ShielddSecurity.TransferPoseidonTailTemplate05Program01
import ShielddSecurity.CompilerWindowRenaming05
import ShielddSecurity.CompilerColumnRenaming05
import ShielddSecurity.CapturedArithmetic45B0014
import ShielddSecurity.CompilerIndexedCopyStream171
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleFirstSparse245B20
open Compiler CompilerAssertionBlock51
open CompilerArithmeticTransport41 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 280).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 424)
   (CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 23076 396 1988) row))
def indices : List Nat := List.range' 3054 16
def localParent : Nat → Option Row
 | 3054 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 24),[(25792,1)]⟩
 | 3055 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 25),[(25793,1)]⟩
 | 3056 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 26),[(25795,1)]⟩
 | 3057 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 27),[(25794,4),(25795,1)]⟩
 | 3058 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 28),[(25796,1)]⟩
 | 3059 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 29),[(25797,1)]⟩
 | 3060 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 30),[(25799,1)]⟩
 | 3061 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 31),[(25798,4),(25799,1)]⟩
 | 3062 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 32),[(25800,1)]⟩
 | 3063 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 33),[(25801,1)]⟩
 | 3064 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 34),[(25803,1)]⟩
 | 3065 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 35),[(25802,4),(25803,1)]⟩
 | 3066 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 36),[(25804,1)]⟩
 | 3067 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 37),[(25805,1)]⟩
 | 3068 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 38),[(25807,1)]⟩
 | 3069 => some ⟨CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value (CapturedArithmetic45B0014.inputs 39),[(25806,4),(25807,1)]⟩
 | _ => none
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem count : rows.length=16 := by rfl
end ShielddSecurity.CapturedMerkleFirstSparse245B20

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B20.rows
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B20.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B20.indices
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B20.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B20.localParent
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B20.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B20.localCheck
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B20.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B20.local_checked
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B20.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleFirstSparse245B20.count
#print axioms ShielddSecurity.CapturedMerkleFirstSparse245B20.count
